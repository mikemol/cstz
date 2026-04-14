"""Tests for cstz.byte_classifier — _classify_byte, _classify_span, factorize_bytes."""
from __future__ import annotations

from pathlib import Path

import pytest
from cstz.legacy.byte_classifier import factorize_bytes, _classify_byte, _classify_span


# ── _classify_byte ───────────────────────────────────────────────────

class TestClassifyByte:
    @pytest.mark.parametrize("byte_val,expected", [
        (0x00, "null"),
        (0x0a, "newline"),
        (0x0d, "cr"),
        (0x20, "space"),
        (0x09, "tab"),
        (0x30, "digit"),      # '0'
        (0x39, "digit"),      # '9'
        (0x35, "digit"),      # '5'
        (0x41, "upper"),      # 'A'
        (0x5a, "upper"),      # 'Z'
        (0x4d, "upper"),      # 'M'
        (0x61, "lower"),      # 'a'
        (0x7a, "lower"),      # 'z'
        (0x6d, "lower"),      # 'm'
        (0x21, "punct"),      # '!'
        (0x2f, "punct"),      # '/'
        (0x7e, "punct"),      # '~'
        (0x3a, "punct"),      # ':'
        (0x01, "control"),    # SOH
        (0x1f, "control"),    # US
        (0x07, "control"),    # BEL
        (0x80, "utf8.cont"),
        (0xbf, "utf8.cont"),
        (0xa0, "utf8.cont"),
        (0xc0, "utf8.2"),
        (0xdf, "utf8.2"),
        (0xc8, "utf8.2"),
        (0xe0, "utf8.3"),
        (0xef, "utf8.3"),
        (0xe5, "utf8.3"),
        (0xf0, "utf8.4"),
        (0xf7, "utf8.4"),
        (0xf4, "utf8.4"),
        (0xf8, "high"),
        (0xff, "high"),
        (0xfb, "high"),
    ])
    def test_classify(self, byte_val: int, expected: str) -> None:
        assert _classify_byte(byte_val) == expected


# ── _classify_span ───────────────────────────────────────────────────

class TestClassifySpan:
    def test_head(self) -> None:
        assert _classify_span(0, 4, 100, 2) == "head.2"

    def test_tail(self) -> None:
        assert _classify_span(96, 4, 100, 2) == "tail.2"

    def test_tail_exact(self) -> None:
        # pos + span == total
        assert _classify_span(96, 4, 100, 2) == "tail.2"

    def test_tail_overflow(self) -> None:
        # pos + span > total
        assert _classify_span(98, 4, 100, 2) == "tail.2"

    def test_body(self) -> None:
        assert _classify_span(50, 4, 100, 2) == "body.2"


# ── factorize_bytes ──────────────────────────────────────────────────

class TestFactorizeBytes:
    def test_empty(self) -> None:
        sppf = factorize_bytes(b"")
        assert sppf.node_count == 0

    def test_single_byte(self) -> None:
        sppf = factorize_bytes(b"\x00")
        assert sppf.node_count == 1

    def test_two_bytes(self) -> None:
        sppf = factorize_bytes(b"ab")
        assert sppf.node_count >= 2  # 2 leaves + at least 1 span

    def test_hello(self) -> None:
        sppf = factorize_bytes(b"Hello, World!")
        assert sppf.node_count > 0

    def test_binary_data(self) -> None:
        sppf = factorize_bytes(bytes(range(256)))
        assert sppf.node_count >= 256

    def test_from_string_path(self, tmp_path: Path) -> None:
        f = tmp_path / "data.bin"
        f.write_bytes(b"test data")
        sppf = factorize_bytes(str(f))
        assert sppf.node_count > 0

    def test_from_path_object(self, tmp_path: Path) -> None:
        f = tmp_path / "data.bin"
        f.write_bytes(b"test data")
        sppf = factorize_bytes(f)
        assert sppf.node_count > 0

    def test_from_memoryview(self) -> None:
        data = b"memview test"
        sppf = factorize_bytes(memoryview(data))
        assert sppf.node_count > 0

    def test_from_bytearray(self) -> None:
        sppf = factorize_bytes(bytearray(b"hello"))
        assert sppf.node_count > 0

    def test_context_width(self) -> None:
        sppf = factorize_bytes(b"abcdef", context_width=2)
        assert sppf.node_count > 0

    def test_chunk_levels_explicit(self) -> None:
        sppf = factorize_bytes(b"abcdef", chunk_levels=2)
        assert sppf.node_count > 0

    def test_chunk_levels_zero(self) -> None:
        """chunk_levels=0 → only leaf nodes, no pairing."""
        sppf = factorize_bytes(b"ab", chunk_levels=0)
        assert sppf.node_count == 2

    def test_odd_length(self) -> None:
        """Odd-length data → last element carried to next level."""
        sppf = factorize_bytes(b"abc")
        assert sppf.node_count >= 3

    def test_context_first_byte(self) -> None:
        """First byte gets dep_type='ctx:^'."""
        sppf = factorize_bytes(b"x")
        assert sppf.nodes[0]['dep_type_raw'] == "ctx:^"

    def test_context_subsequent_byte(self) -> None:
        """Bytes after first use hex context."""
        sppf = factorize_bytes(b"ab", context_width=4)
        raw = sppf.nodes[1]['dep_type_raw']
        assert raw.startswith("ctx:")
        assert raw != "ctx:^"

    def test_large_data_level_cap(self) -> None:
        """Large data → chunk_levels capped at 20."""
        data = bytes(2**21)  # 2M bytes
        sppf = factorize_bytes(data, chunk_levels=1)
        # Just verify it doesn't blow up with explicit cap
        assert sppf.node_count > 0

    def test_summary(self) -> None:
        sppf = factorize_bytes(b"Hello, World!")
        text = sppf.summary()
        assert "SPPF:" in text

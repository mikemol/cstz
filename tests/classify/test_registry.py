"""Tests for cstz.classify.registry — the semantic vocabulary lock."""

import pytest
from cstz.classify.registry import Discriminator, DiscriminatorRegistry


class TestDiscriminator:
    def test_frozen(self):
        """Discriminator is frozen — mutation should fail."""
        d = Discriminator(id=1, name="x", doc="", fires=lambda n: True)
        with pytest.raises((AttributeError, TypeError)):
            d.id = 2  # type: ignore

    def test_version_default(self):
        d = Discriminator(id=1, name="x", doc="", fires=lambda n: True)
        assert d.version == 1

    def test_fields(self):
        d = Discriminator(
            id=4, name="foo", doc="something meaningful",
            fires=lambda n: n > 0, version=2,
        )
        assert d.id == 4
        assert d.name == "foo"
        assert d.doc == "something meaningful"
        assert d.version == 2
        assert d.fires(5) is True
        assert d.fires(-1) is False


class TestRegistryRegistration:
    def test_empty_registry(self):
        reg = DiscriminatorRegistry()
        assert len(reg) == 0
        assert reg.all() == []

    def test_register_assigns_one_hot(self):
        """IDs are 1 << k, assigned in registration order."""
        reg = DiscriminatorRegistry()
        d0 = reg.register("d0", lambda n: True)
        d1 = reg.register("d1", lambda n: False)
        d2 = reg.register("d2", lambda n: True)
        assert d0 == 0b001
        assert d1 == 0b010
        assert d2 == 0b100

    def test_register_returns_id(self):
        reg = DiscriminatorRegistry()
        d_id = reg.register("x", lambda n: True)
        assert isinstance(d_id, int)
        assert d_id == 1

    def test_register_stores_metadata(self):
        reg = DiscriminatorRegistry()
        reg.register("x", lambda n: n, doc="is truthy", version=2)
        d = reg.get_by_name("x")
        assert d.name == "x"
        assert d.doc == "is truthy"
        assert d.version == 2

    def test_len(self):
        reg = DiscriminatorRegistry()
        assert len(reg) == 0
        reg.register("a", lambda n: True)
        assert len(reg) == 1
        reg.register("b", lambda n: True)
        assert len(reg) == 2


class TestRegistryLookup:
    def test_get_by_id(self):
        reg = DiscriminatorRegistry()
        d_id = reg.register("foo", lambda n: n == "foo")
        d = reg.get(d_id)
        assert d.name == "foo"
        assert d.fires("foo") is True
        assert d.fires("bar") is False

    def test_get_by_name(self):
        reg = DiscriminatorRegistry()
        reg.register("foo", lambda n: True)
        d = reg.get_by_name("foo")
        assert d.name == "foo"

    def test_get_missing_id_raises(self):
        reg = DiscriminatorRegistry()
        reg.register("foo", lambda n: True)
        with pytest.raises(KeyError):
            reg.get(999)

    def test_get_missing_name_raises(self):
        reg = DiscriminatorRegistry()
        with pytest.raises(KeyError):
            reg.get_by_name("nonexistent")

    def test_contains(self):
        reg = DiscriminatorRegistry()
        d_id = reg.register("x", lambda n: True)
        assert d_id in reg
        assert 999 not in reg

    def test_all_preserves_order(self):
        reg = DiscriminatorRegistry()
        names = ["a", "b", "c", "d", "e"]
        for name in names:
            reg.register(name, lambda n: True)
        assert [d.name for d in reg.all()] == names


class TestRegistryStability:
    """Stability invariant: once registered, a discriminator cannot
    be replaced or remapped."""

    def test_duplicate_name_rejected(self):
        reg = DiscriminatorRegistry()
        reg.register("x", lambda n: True)
        with pytest.raises(ValueError, match="already registered"):
            reg.register("x", lambda n: False)

    def test_duplicate_name_preserves_original(self):
        reg = DiscriminatorRegistry()
        reg.register("x", lambda n: True, doc="original")
        try:
            reg.register("x", lambda n: False, doc="replacement")
        except ValueError:
            pass
        # Original must survive
        d = reg.get_by_name("x")
        assert d.doc == "original"
        assert d.fires(None) is True

    def test_ids_are_stable(self):
        """Re-registering a name fails; IDs never re-assigned."""
        reg = DiscriminatorRegistry()
        d_id = reg.register("x", lambda n: True)
        assert reg.get(d_id).name == "x"
        try:
            reg.register("x", lambda n: False)
        except ValueError:
            pass
        assert reg.get(d_id).name == "x"  # still the original


class TestRegistryComparability:
    """Comparability across classifiers: one registry, shared IDs."""

    def test_two_discriminators_get_distinct_ids(self):
        reg = DiscriminatorRegistry()
        a = reg.register("a", lambda n: True)
        b = reg.register("b", lambda n: True)
        assert a != b
        assert a & b == 0  # one-hot: no shared bits

    def test_union_of_ids_is_bitmask_or(self):
        """Multiple discriminator IDs OR together cleanly (no overlap)."""
        reg = DiscriminatorRegistry()
        ids = [reg.register(f"d{i}", lambda n: True) for i in range(5)]
        mask = 0
        for d_id in ids:
            mask |= d_id
        assert mask == 0b11111  # all 5 bits set, no collisions

#!/usr/bin/env bash
# Run the full paper ↔ Agda ↔ Python alignment pipeline, end-to-end.
#
# Stage 0 — extract manifests from each source (parser-based, no regex):
#     paper/**.tex  → pandoc JSON AST   → reports/paper_decls.jsonl
#     agda/**.agda  → tree-sitter-agda  → reports/agda_decls.jsonl
#     src/cstz/**.py → python ast       → reports/python_decls.jsonl
#
# Stage 1 — calibrate discriminator-family weights against the
#   citation oracle (app_f_trace.py feedback-loop pattern).
#
# Stage 2 — align paper × agda × python using the ParallelRegistry
#   with calibrated weights.  Produces triples.jsonl + residues.jsonl.
#
# Stage 3 — validate committed triples against authorial citations;
#   classify each into its Belnap-lattice tier.
#
# Stage 4 — gap analysis: 3×3 cofiber cells + near-triples + conflicts.
#
# Stage 5 — render human-readable reports.

set -euo pipefail

cd "$(dirname "$0")/.."

STRUCTURAL=0
for arg in "$@"; do
    case "$arg" in
        --structural) STRUCTURAL=1 ;;
        *) echo "unknown arg: $arg" >&2; exit 1 ;;
    esac
done

if [ "$STRUCTURAL" -eq 1 ]; then
    OUT=reports/structural
    CALIB_FLAG=--structural-only
    ALIGN_FLAG=--structural-only
    mode="STRUCTURAL-ONLY"
else
    OUT=reports
    CALIB_FLAG=
    ALIGN_FLAG=
    mode="LEXICAL (default)"
fi

mkdir -p "$OUT"
echo "== Mode: $mode  out=$OUT =="

echo
echo "== Stage 0: extracting manifests =="
# The extractors always write to reports/ (the manifests are mode-
# independent).  Other stages consume them from reports/.
python3 scripts/extract_paper.py   > reports/paper_decls.jsonl 2>/dev/null
python3 scripts/extract_agda.py    > reports/agda_decls.jsonl  2>/dev/null
python3 scripts/extract_python.py  > reports/python_decls.jsonl 2>/dev/null
wc -l reports/paper_decls.jsonl reports/agda_decls.jsonl reports/python_decls.jsonl

echo
echo "== Stage 1: calibrating discriminator-family weights =="
python3 scripts/calibrate_weights.py $CALIB_FLAG 2>&1 | grep -E "^(iter|#)" || true

echo
echo "== Stage 2: parallel-discriminator alignment =="
python3 scripts/align_parallel.py $ALIGN_FLAG 2>&1 | grep -E "^(#|  \")" || true

echo
echo "== Stage 3: validating against authorial citations =="
# validate_against_comments.py reads triples.jsonl; set OUT_DIR so it
# picks the right one.
OUT_DIR=$OUT python3 scripts/validate_against_comments.py 2>&1 | head -25

echo
echo "== Stage 4: gap / cofiber-cell analysis =="
OUT_DIR=$OUT python3 scripts/gap_analysis.py 2>&1

echo
echo "== Stage 5: rendering reports =="
OUT_DIR=$OUT python3 scripts/write_reports.py 2>&1

echo
echo "Done.  See $OUT/{pipeline,triples,gaps,conflicts,validation,cofiber,residues}.md"

if [ "$STRUCTURAL" -eq 1 ]; then
    echo
    echo "== Writing structural-vs-lexical comparison =="
    python3 scripts/structural_vs_lexical.py 2>&1 || true
fi

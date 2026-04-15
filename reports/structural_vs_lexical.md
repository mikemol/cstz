# Lexical vs. structural-only alignment comparison

This report compares two runs of the full pipeline:

- **Lexical** (default): all discriminator families active
  (`token`, `name_tok`, `cite`, `kind`, `edge`, plus κ-evolved primitives)
- **Structural-only** (`--structural`): lexical families masked;
  only `kind`, `edge`, `subtree_shape`, and residue-driven wedges

The point of the comparison: if lexical families account for the
bulk of alignment, the paper/agda/python triple is held together
mostly by shared naming conventions.  If structural-only still
delivers substantial agreement, the three sources share real
parse-tree topology for the common concepts.  Per Paper Def 9.8
(evidence semantics), neither mode's 'silence' is evidence
against the triple — they're measurements at different levels.

## Registry sizes

| Mode | Total discriminators | Families |
|------|---------------------|----------|
| Lexical | 3407 | {'token': 2000, 'name_tok': 465, 'kind': 137, 'edge': 398, 'source': 3, 'cite': 316, 'subtree_shape_p1': 44, 'subtree_shape_p2_DROPPED': 44} |
| Structural | 626 | {'kind': 137, 'edge': 398, 'source': 3, 'subtree_shape_p1_DROPPED': 44, 'subtree_shape_p2_DROPPED': 44} |

## Calibration outcomes

| Mode | Iterations | Final top-1 accuracy | Final mean rank |
|------|-----------|---------------------|----------------|
| Lexical | 7 | 79.1% | 1.233 |
| Structural | 3 | 0.0% | 0.000 |

## Committed triples

| Mode | Tier 1 | Tier 2 | Total | Cited | Citation rate |
|------|--------|--------|-------|-------|---------------|
| Lexical | 30 | 71 | 101 | 72 | 71.3% |
| Structural | 0 | 0 | 0 | 0 | 0.0% |

## Triple-set agreement

Are the two modes finding the same triples?

| Partition | Count |
|-----------|-------|
| Both modes (consensus) | 0 |
| Lexical-only | 100 |
| Structural-only | 0 |

**Consensus triples are the highest-confidence subset** — they
are supported by both lexical and structural signal.  Lexical-
only triples rely on shared naming; structural-only triples rely
on parse-tree topology without lexical agreement (these are
interesting because they imply structural match without nominal
agreement, e.g. an Agda record and a Python dataclass that share
field-kind shape but not field names).

## Cofiber-cell counts

| Cell | Lexical | Structural |
|------|---------|------------|
| E/E/M | 39 | 82 |
| E/M/E | 54 | 91 |
| M/E/E | 106 | 123 |
| near-triple | 111 | 183 |

## Wedge-grade articulation (structural only)

(No wedges articulated — calibration terminated without plateau.)

## Sample consensus triples (structural AND lexical agree)

| Agda | Paper | Python |
|------|-------|--------|

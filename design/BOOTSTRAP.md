# Session bootstrap — CSTZ alignment rebuild

If you are a new Claude session picking up this project, do NOT re-read the
full git log or try to reconstruct the design history from conversation.
The design space has been externalized to this directory as a SPPF (shared
packed parse forest) of JSONL records.

## Minimum context to load

```bash
# Human-readable catalog of every principle / decision / rejection / question
python scripts/design_sppf.py index

# The open questions blocking further code
python scripts/design_sppf.py questions

# The active architectural principles you must not violate
python scripts/design_sppf.py principles
```

That alone should get you oriented. A full session's conversation history is
tens of thousands of tokens; the SPPF slice above is under two thousand.

## Working on a specific decision

```bash
# Full detail of one node
python scripts/design_sppf.py show d-single-closed-loop-module

# Minimal slice needed to understand a node (transitive parents)
python scripts/design_sppf.py deps d-single-closed-loop-module

# Everything that would be affected by changing a node
python scripts/design_sppf.py dependents p-flat-k-pool
```

## When you make a new decision / correction / rejection

Append a record to the corresponding `design/*.jsonl` file. Each record must
have `id`, `type`, `title`, `body`, `parents` (ids of nodes this depends on),
`status`, and optionally `refs` (paper citations, file:line, etc).

Use `scripts/design_sppf.py supersede <old_id> <new_record.json>` to retire
an old node without deleting it — the graph preserves provenance.

## Current status (2026-04-15)

- SPPF scaffolding: done.
- `scripts/closed_loop.py`: **not yet implemented**. Blocked on three open
  questions that must be resolved with the user before `step()` can be
  specified:
  1. `q-tau-sigma-wedge-combinator` — how do τ and σ of a grade-2 wedge
     derive from its parents' τ/σ under the "atoms start τ = σ" decision?
  2. `q-wedge-articulation-signal` — what distributional signal triggers
     wedge articulation, without smuggling a commit gate back in?
  3. `q-weight-gradient-direction` — what scalar does weight adjustment
     gradient-descend on if not rank-residue?
- Prior multi-stage pipeline (`scripts/align_parallel.py` etc.) is PRESERVED
  under `reports/` and `reports/structural/` as comparison artifacts. Do not
  modify those scripts unless explicitly asked; the closed-loop rebuild is
  an independent module.

## Do not re-litigate closed decisions

Everything in `design/rejected.jsonl` has been explicitly taken off the
table by user direction. Before proposing any architectural alternative,
check whether it's already there. Re-proposing rejected designs costs
context and erodes trust.

Specifically: no source-qualified kinds, no per-family weight scaling, no
lowercase (or any) canonicalization, no hand-coded arity features, no
hand-coded axiom matchers, no max_iters, no commit/tier/triple outputs.

## The meta-principle above everything

The paper claims self-hosting: its framework's machinery generates
recognizers for increasingly abstract structures without external
classification (App B §B.39). The rebuild must be an instance of this,
not a parallel track. Every hand-written recognizer anywhere in the
pipeline — at any level — breaks that claim.

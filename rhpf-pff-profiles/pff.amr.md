# PFF / RHPF AMR projection profile

This is a *projection* profile, not the canonical storage model.

AMR, as introduced by Banarescu et al. (2013), is a rooted directed acyclic graph
notation for semantic structure. That makes it useful for human-readable local
views of a PFF document: a patch, an address lineage slice, a merge explanation,
or a shadow node explanation. It is not a good canonical carrier for the whole
ranked higher object because absolute identity, revision lineage, and higher-path
coherences are not native AMR primitives.

## Normative scope

The normative PFF information model is flat and document-scoped. AMR is only a
projection of selected slices of that flat model.

## Rule of use

Use AMR to export:
- one patch
- one addr0 lineage
- one addr1 explanation
- one shadow node with its packed alternatives

Do not use AMR as the sole interchange form for the full document.

## Mapping

PFF concept        -> AMR node / edge
Document           -> (d / pff-document ...)
Rank               -> (r / rank :ord n)
Patch              -> (p / patch :id "g7" :phase "merge" ...)
Boundary           -> (b / boundary ...)
Chart              -> (c / chart :root "r0" ...)
Addr0              -> (a / addr0 :id "a17" ...)
Segment            -> :seg (s / seg ...)
Pair               -> :pair (q / pair ...)
Step               -> ordered subgraph with :ord
Addr1              -> (e / path1 :ctor "glue" :src a17 :dst a24 ...)
Addr2              -> (k / path2 :ctor "coh" :src e31 :dst e44 ...)
Shadow             -> (s / shadow ...)
ShadowNode         -> (n / semantic-node | packed-node | intermediate-node)

## Losslessness discipline

Penman edge order is not semantic, so every repeated child list must carry an
explicit ordinal:
- :seg (s / seg :ord 0 ...)
- :pair (q / pair :ord 1 ...)
- :step (t / step :ord 0 :kind "child" :arg 2)

External IDs remain mandatory:
- addr0 IDs
- patch IDs
- rank IDs
- path IDs

## Canonical route representation

The canonical PFF route form is the structured step sequence used in JSON and
SQL. A dotted text form such as `child(2).field(lhs)` is a derived convenience
serialization. When AMR is emitted from a canonical route, preserve step order
explicitly via `:ord`; when AMR is parsed back, reconstruct the ordered step
sequence first and only then, optionally, regenerate the dotted text form.

## Example: one absolute 0-address

```penman
(a17 / addr0
   :id "a17"
   :sort "literal"
   :seg (s2 / seg
           :ord 0
           :rank (r2 / rank :id "r2" :ord 2)
           :phase "discover"
           :patch (g2 / patch :id "g2")
           :pair (q20 / pair
                    :ord 0
                    :role "principal"
                    :chart (c0 / chart :id "c0" :root "r0")
                    :root "r0"
                    :step (t0 / step :ord 0 :kind "child" :arg 2)
                    :step (t1 / step :ord 1 :kind "field" :arg "lhs")))
   :seg (s7 / seg
           :ord 1
           :rank (r7 / rank :id "r7" :ord 7)
           :phase "merge"
           :patch (g7 / patch :id "g7")
           :pair (q71 / pair
                    :ord 0
                    :role "aux"
                    :chart (c1 / chart :id "c1" :root "r9")
                    :root "r9"
                    :step (u0 / step :ord 0 :kind "child" :arg 0)
                    :step (u1 / step :ord 1 :kind "port" :arg "out"))))
```

## Example: one merge / glue witness

```penman
(e31 / path1
   :id "e31"
   :ctor "glue"
   :rank (r7 / rank :id "r7" :ord 7)
   :src a17
   :dst (a24 / addr0 :id "a24")
   :boundary (b1 / boundary :id "b1"))
```

## Recommended use

Export AMR from:
1. an RDF graph slice,
2. a SQL view,
3. or a JSON document subtree.

Treat it as a lens for human inspection and LLM interaction, not as the
authoritative store.

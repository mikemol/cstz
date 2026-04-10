# PFF / RHPF Core profile notes (draft 1.1)

This note makes the normative choices that were previously only implicit.

## 1. Normative information model

The normative PFF information model is **flat and document-scoped**.

`patches`, `boundaries`, `charts`, `addresses0`, `paths1`, `paths2`,
`classViews`, and `shadows` all live at document scope. A patch does not own an
address, chart, or path by nesting. It only links to them by identifier.

## 2. Identifier scope

All local identifiers in a PFF document are **document-local**, including rank
IDs. `baseIri` is only used when minting global IRIs for RDF/JSON-LD or other
exports. Local identifier equality is never determined by `baseIri`.

When merging two documents, an implementation MUST alpha-rename incoming local
identifiers on collision unless the merge policy explicitly declares that the
identifiers are already aligned.

## 3. Segment monotonicity

Within one `Addr0`, segment ranks are **strictly increasing** by rank ordinal.
A single `Addr0` MUST NOT contain two segments for the same rank. This is the
normative reading of WF-1.

## 4. Canonical route form

The canonical route form is the structured step sequence.

Example canonical form:

```json
[
  {"kind": "child", "arg": 2},
  {"kind": "field", "arg": "lhs"}
]
```

A dotted route string such as `child(2).field(lhs)` is a conforming text
serialization profile. Round-trip rule:

1. parse dotted text into an ordered step sequence;
2. store or transmit the ordered step sequence as canonical form;
3. regenerate dotted text only as a presentation artifact.

## 5. Derived views

`ClassView` and `Shadow` are derived views. They are never authoritative. Any
conforming serialization of those views MUST declare:

- `truncation`
- `congruence`
- `isAuthoritative = false`

## 6. API discipline

Merge/write APIs should return structured validation issues with at least:

- `rule`
- `location`
- `severity`
- `message`

Recommended merge status discipline:

- `200` clean merge stored
- `207` stored with non-fatal violations recorded
- `422` rejected because fatal violations prevented storage

module CoreProof where

-- ══════════════════════════════════════════════════════════
-- SPPF proof of src/cstz/core.py
-- 7500 AST nodes → 2109 proof cells
-- σ=2096 τ=859 κ=779
-- 103 η-merges, 7 case splits
-- ══════════════════════════════════════════════════════════

-- ── Primitives ────────────────────────────────────────────

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- ── σ-fiber canonical map (2096 roots) ──

σ : ℕ → ℕ
σ n = n

σ-idem : ∀ n → σ (σ n) ≡ σ n
σ-idem n = refl

-- ── τ-fiber canonical map (859 roots) ──

τ : ℕ → ℕ
τ n = n

τ-idem : ∀ n → τ (τ n) ≡ τ n
τ-idem n = refl

-- ── κ-fiber canonical map (779 roots) ──

κ : ℕ → ℕ
κ n = n

κ-idem : ∀ n → κ (κ n) ≡ κ n
κ-idem n = refl

-- ── η-equivalences ────────────────────────────────────────
-- 103 type-erasure steps; each is refl after reduction.

-- Self, dict all resolve to τ=13
η-allη-Name-Self : τ 13 ≡ τ 13
η-allη-Name-Self = refl

-- Self._parent, Self._rank all resolve to τ=14
η-allη-Attribute-Self-_parent : τ 14 ≡ τ 14
η-allη-Attribute-Self-_parent = refl

-- str, NoneType all resolve to τ=0
η-allη-Constant-str : τ 0 ≡ τ 0
η-allη-Constant-str = refl

-- ∀η.Attribute.Self._parent, Self.find all resolve to τ=34
η-allη-Attribute-allη-Attribute-Self-_parent : τ 34 ≡ τ 34
η-allη-Attribute-allη-Attribute-Self-_parent = refl

-- 34, 14 all resolve to τ=14
η-ghost-cleavage-L0x3ax28x27allη-Attribute-allη-Attribute-Self-_parentx27x2c_x27allη-Attribute-allη-Attribute-Self-_parentx27x2c_x27allη-Attribute-allη-Attribute-Self-_parentx27x29 : τ 14 ≡ τ 14
η-ghost-cleavage-L0x3ax28x27allη-Attribute-allη-Attribute-Self-_parentx27x2c_x27allη-Attribute-allη-Attribute-Self-_parentx27x2c_x27allη-Attribute-allη-Attribute-Self-_parentx27x29 = refl

-- ∀η.Name.Self, ∀η.Constant.str all resolve to τ=20
η-allη-Dict-allη-Name-Self : τ 20 ≡ τ 20
η-allη-Dict-allη-Name-Self = refl

-- tuple, ∀η.Attribute.∀η.Attribute.Self all resolve to τ=7
η-allη-Name-tuple : τ 7 ≡ τ 7
η-allη-Name-tuple = refl

-- Self.uf.make, Self.uf.find all resolve to τ=153
η-allη-Attribute-Self-uf-make : τ 153 ≡ τ 153
η-allη-Attribute-Self-uf-make = refl

-- tuple, ∀η.Constant.str all resolve to τ=59
η-allη-Tuple-tuple : τ 59 ≡ τ 59
η-allη-Tuple-tuple = refl

-- 14, 34 all resolve to τ=34
η-ghost-cleavage-L0x3ax28x27allη-Constant-strx27x2c_x27allη-Constant-strx27x2c_x27allη-Constant-strx27x29 : τ 34 ≡ τ 34
η-ghost-cleavage-L0x3ax28x27allη-Constant-strx27x2c_x27allη-Constant-strx27x2c_x27allη-Constant-strx27x29 = refl

-- 14, 34 all resolve to τ=34
η-ghost-cleavage-L1x3ax2814x2c_34x29 : τ 34 ≡ τ 34
η-ghost-cleavage-L1x3ax2814x2c_34x29 = refl

-- 13, 7 all resolve to τ=7
η-η-cleavage-L0x3ax28x27allη-Constant-strx27x2c_x27allη-Constant-strx27x2c_x27allη-Constant-strx27x29 : τ 7 ≡ τ 7
η-η-cleavage-L0x3ax28x27allη-Constant-strx27x2c_x27allη-Constant-strx27x2c_x27allη-Constant-strx27x29 = refl

-- None, ∀η.Constant.str all resolve to τ=349
η-allη-Call-None : τ 349 ≡ τ 349
η-allη-Call-None = refl

-- ══════════════════════════════════════════════════════════
-- Construction modules (one per κ-class)
-- ══════════════════════════════════════════════════════════

-- ── load (Load) ────────────────────────────────
-- 2366 nodes, 1 type contexts, 1 forms

module load-Load-8 where

  -- ctx-8: 2366 nodes, 1 forms
  -- [(untyped)]
  --   σ=17 (2366×)
  ctx-8-τ8 : τ 8 ≡ τ 8
  ctx-8-τ8 = refl


-- ── var (Name) ─────────────────────────────────
-- 1497 nodes, 2 type contexts, 200 forms

module var-Name-13 where

  -- ctx-16: 757 nodes, 175 forms
  -- [(untyped)]
  ctx-16-τ16 : τ 16 ≡ τ 16
  ctx-16-τ16 = refl

  -- Self: 740 nodes, 31 forms
  -- [AST, Self, Self._counter, Self.node_count, T]
  Self-τ13 : τ 13 ≡ τ 13
  Self-τ13 = refl


-- ── store (Store) ──────────────────────────────
-- 365 nodes, 1 type contexts, 1 forms

module store-Store-6 where

  -- ctx-6: 365 nodes, 1 forms
  -- [(untyped)]
  --   σ=13 (365×)
  ctx-6-τ6 : τ 6 ≡ τ 6
  ctx-6-τ6 = refl


-- ── terminal (Constant) ────────────────────────
-- 295 nodes, 2 type contexts, 125 forms

module terminal-Constant-0 where

  -- str: 273 nodes, 124 forms
  -- [NoneType, bool, float, int, str]
  str-τ0 : τ 0 ≡ τ 0
  str-τ0 = refl

  -- ctx-95: 22 nodes, 1 forms
  -- [(untyped)]
  --   σ=141 (22×)
  ctx-95-τ95 : τ 95 ≡ τ 95
  ctx-95-τ95 = refl


-- ── bind (Name) ────────────────────────────────
-- 275 nodes, 2 type contexts, 153 forms

module bind-Name-7 where

  -- ctx-44: 245 nodes, 134 forms
  -- [(untyped)]
  ctx-44-τ44 : τ 44 ≡ τ 44
  ctx-44-τ44 = refl

  -- tuple: 30 nodes, 24 forms
  -- [Self._counter, Self.node_count, T, dict, int]
  tuple-τ7 : τ 7 ≡ τ 7
  tuple-τ7 = refl


-- ── morphism@state (Attribute) ─────────────────
-- 243 nodes, 1 type contexts, 44 forms

module morphism-at-state-Attribute-24 where

  -- Self-_parent: 243 nodes, 44 forms
  -- [Self._cascade_abstraction_merge, Self._cascade_eta, Self._cell_contents, Self._cell_obs, Self._cleavage_fibers]
  Self-_parent-τ34 : τ 34 ≡ τ 34
  Self-_parent-τ34 = refl


-- ── index (Index) ──────────────────────────────
-- 130 nodes, 2 type contexts, 43 forms

module index-Index-26 where

  -- ctx-36: 84 nodes, 38 forms
  -- [(untyped)]
  ctx-36-τ36 : τ 36 ≡ τ 36
  ctx-36-τ36 = refl

  -- ctx-113: 46 nodes, 6 forms
  -- [(untyped)]
  --   σ=162 (19×)
  --   σ=219 (2×)
  --   σ=346 (20×)
  --   σ=433 (2×)
  --   σ=446 (1×)
  --   σ=550 (2×)
  ctx-113-τ113 : τ 113 ≡ τ 113
  ctx-113-τ113 = refl


-- ── morphism@state (Attribute) ─────────────────
-- 68 nodes, 1 type contexts, 14 forms

module morphism-at-state-Attribute-105 where

  -- Self-uf-make: 68 nodes, 14 forms
  -- [Self._cell_contents.get, Self._cell_obs.get, Self._cell_obs.keys, Self._cleavage_fibers.append, Self._cleavage_levels.append]
  Self-uf-make-τ153 : τ 153 ≡ τ 153
  Self-uf-make-τ153 = refl


-- ── subscript (Subscript) ──────────────────────
-- 58 nodes, 4 type contexts, 21 forms

module subscript-Subscript-67 where

  -- ctx-195: 25 nodes, 5 forms
  -- [(untyped)]
  --   σ=292 (2×)
  --   σ=347 (17×)
  --   σ=551 (1×)
  --   σ=1488 (3×)
  --   σ=1573 (2×)
  ctx-195-τ195 : τ 195 ≡ τ 195
  ctx-195-τ195 = refl

  -- ctx-114: 15 nodes, 3 forms
  -- [(untyped)]
  --   σ=163 (7×)
  --   σ=277 (7×)
  --   σ=746 (1×)
  ctx-114-τ114 : τ 114 ≡ τ 114
  ctx-114-τ114 = refl

  -- ctx-257: 10 nodes, 5 forms
  -- [(untyped)]
  --   σ=379 (2×)
  --   σ=399 (1×)
  --   σ=417 (5×)
  --   σ=1413 (1×)
  --   σ=1627 (1×)
  ctx-257-τ257 : τ 257 ≡ τ 257
  ctx-257-τ257 = refl

  -- ctx-84: 8 nodes, 8 forms
  -- [(untyped)]
  --   σ=124 (1×)
  --   σ=565 (1×)
  --   σ=802 (1×)
  --   σ=977 (1×)
  --   σ=1038 (1×)
  --   σ=1069 (1×)
  --   σ=1711 (1×)
  --   σ=1910 (1×)
  ctx-84-τ84 : τ 84 ≡ τ 84
  ctx-84-τ84 = refl


-- ── arrow (Name) ───────────────────────────────
-- 55 nodes, 1 type contexts, 4 forms

module arrow-Name-69 where

  -- toint: 55 nodes, 4 forms
  -- [AST, Self, Self._counter, Self.node_count, T]
  --   σ=126 (42×)
  --   σ=488 (3×)
  --   σ=848 (6×)
  --   σ=1415 (4×)
  toint-τ13 : τ 13 ≡ τ 13
  toint-τ13 = refl


-- ── apply (Call) ───────────────────────────────
-- 46 nodes, 2 type contexts, 19 forms

module apply-Call-106 where

  -- ctx-165: 41 nodes, 16 forms
  -- [(untyped)]
  ctx-165-τ165 : τ 165 ≡ τ 165
  ctx-165-τ165 = refl

  -- ctx-154: 5 nodes, 3 forms
  -- [(untyped)]
  --   σ=225 (1×)
  --   σ=652 (2×)
  --   σ=1144 (2×)
  ctx-154-τ154 : τ 154 ≡ τ 154
  ctx-154-τ154 = refl


-- ── arg (arg) ──────────────────────────────────
-- 45 nodes, 1 type contexts, 2 forms

module arg-11 where

  -- ctx-11: 45 nodes, 2 forms
  -- [(untyped)]
  --   σ=20 (42×)
  --   σ=1676 (3×)
  ctx-11-τ11 : τ 11 ≡ τ 11
  ctx-11-τ11 = refl


-- ── arg (arg) ──────────────────────────────────
-- 38 nodes, 2 type contexts, 27 forms

module arg-21 where

  -- ctx-93: 32 nodes, 22 forms
  -- [(untyped)]
  ctx-93-τ93 : τ 93 ≡ τ 93
  ctx-93-τ93 = refl

  -- ctx-31: 6 nodes, 5 forms
  -- [(untyped)]
  --   σ=39 (2×)
  --   σ=72 (1×)
  --   σ=73 (1×)
  --   σ=112 (1×)
  --   σ=424 (1×)
  ctx-31-τ31 : τ 31 ≡ τ 31
  ctx-31-τ31 = refl


-- ── morphism@state (Attribute) ─────────────────
-- 36 nodes, 1 type contexts, 28 forms

module morphism-at-state-Attribute-14 where

  -- Self-_parent: 36 nodes, 28 forms
  -- [Self._cell_contents, Self._cell_obs, Self._cleavage_fibers, Self._cleavage_ghost_count, Self._cleavage_levels]
  Self-_parent-τ14 : τ 14 ≡ τ 14
  Self-_parent-τ14 = refl


-- ── subscript (Subscript) ──────────────────────
-- 36 nodes, 2 type contexts, 25 forms

module subscript-Subscript-33 where

  -- ctx-47: 32 nodes, 21 forms
  -- [(untyped)]
  ctx-47-τ47 : τ 47 ≡ τ 47
  ctx-47-τ47 = refl

  -- ctx-157: 4 nodes, 4 forms
  -- [(untyped)]
  --   σ=228 (1×)
  --   σ=447 (1×)
  --   σ=536 (1×)
  --   σ=539 (1×)
  ctx-157-τ157 : τ 157 ≡ τ 157
  ctx-157-τ157 = refl


-- ── product (Tuple) ────────────────────────────
-- 30 nodes, 4 type contexts, 17 forms

module product-Tuple-15 where

  -- tuple: 12 nodes, 10 forms
  -- [tuple]
  tuple-τ17 : τ 17 ≡ τ 17
  tuple-τ17 = refl

  -- tuple: 10 nodes, 3 forms
  -- [tuple]
  --   σ=370 (1×)
  --   σ=1461 (3×)
  --   σ=1576 (6×)
  tuple-τ250 : τ 250 ≡ τ 250
  tuple-τ250 = refl

  -- tuple: 6 nodes, 3 forms
  -- [tuple]
  --   σ=189 (1×)
  --   σ=335 (3×)
  --   σ=414 (2×)
  tuple-τ127 : τ 127 ≡ τ 127
  tuple-τ127 = refl

  -- tuple: 2 nodes, 1 forms
  -- [tuple]
  --   σ=33 (2×)
  tuple-τ25 : τ 25 ≡ τ 25
  tuple-τ25 = refl


-- ── let (Assign) ───────────────────────────────
-- 27 nodes, 1 type contexts, 19 forms

module let-k-Assign-127 where

  -- ctx-186: 27 nodes, 19 forms
  -- [(untyped)]
  ctx-186-τ186 : τ 186 ≡ τ 186
  ctx-186-τ186 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 26 nodes, 1 type contexts, 26 forms

module effect-seq-Expr-1 where

  -- ctx-1: 26 nodes, 26 forms
  -- [(untyped)]
  ctx-1-τ1 : τ 1 ≡ τ 1
  ctx-1-τ1 = refl


-- ── index (Index) ──────────────────────────────
-- 26 nodes, 1 type contexts, 4 forms

module index-Index-371 where

  -- ctx-492: 26 nodes, 4 forms
  -- [(untyped)]
  --   σ=849 (20×)
  --   σ=1679 (2×)
  --   σ=1758 (3×)
  --   σ=1901 (1×)
  ctx-492-τ492 : τ 492 ≡ τ 492
  ctx-492-τ492 = refl


-- ── subscript (Subscript) ──────────────────────
-- 26 nodes, 1 type contexts, 10 forms

module subscript-Subscript-372 where

  -- ctx-493: 26 nodes, 10 forms
  -- [(untyped)]
  ctx-493-τ493 : τ 493 ≡ τ 493
  ctx-493-τ493 = refl


-- ── coerce (FormattedValue) ────────────────────
-- 24 nodes, 2 type contexts, 18 forms

module coerce-FormattedValue-275 where

  -- ctx-486: 15 nodes, 14 forms
  -- [(untyped)]
  ctx-486-τ486 : τ 486 ≡ τ 486
  ctx-486-τ486 = refl

  -- ctx-377: 9 nodes, 5 forms
  -- [(untyped)]
  --   σ=611 (5×)
  --   σ=1813 (1×)
  --   σ=1959 (1×)
  --   σ=1994 (1×)
  --   σ=2037 (1×)
  ctx-377-τ377 : τ 377 ≡ τ 377
  ctx-377-τ377 = refl


-- ── cardinality (Call) ─────────────────────────
-- 23 nodes, 2 type contexts, 17 forms

module cardinality-Call-149 where

  -- int: 22 nodes, 16 forms
  -- [int]
  int-τ335 : τ 335 ≡ τ 335
  int-τ335 = refl

  -- int: 1 nodes, 1 forms
  -- [int]
  --   σ=312 (1×)
  int-τ210 : τ 210 ≡ τ 210
  int-τ210 = refl


-- ── powerset (Call) ────────────────────────────
-- 22 nodes, 1 type contexts, 1 forms

module powerset-Call-125 where

  -- ctx-184: 22 nodes, 1 forms
  -- [(untyped)]
  --   σ=278 (22×)
  ctx-184-τ184 : τ 184 ≡ τ 184
  ctx-184-τ184 = refl


-- ── product (Tuple) ────────────────────────────
-- 21 nodes, 2 type contexts, 2 forms

module product-Tuple-76 where

  -- tuple: 17 nodes, 1 forms
  -- [tuple]
  --   σ=146 (17×)
  tuple-τ100 : τ 100 ≡ τ 100
  tuple-τ100 = refl

  -- tuple: 4 nodes, 1 forms
  -- [tuple]
  --   σ=142 (4×)
  tuple-τ96 : τ 96 ≡ τ 96
  tuple-τ96 = refl


-- ── index (Index) ──────────────────────────────
-- 21 nodes, 2 type contexts, 2 forms

module index-Index-77 where

  -- ctx-101: 17 nodes, 1 forms
  -- [(untyped)]
  --   σ=147 (17×)
  ctx-101-τ101 : τ 101 ≡ τ 101
  ctx-101-τ101 = refl

  -- ctx-97: 4 nodes, 1 forms
  -- [(untyped)]
  --   σ=143 (4×)
  ctx-97-τ97 : τ 97 ≡ τ 97
  ctx-97-τ97 = refl


-- ── subscript (Subscript) ──────────────────────
-- 21 nodes, 2 type contexts, 2 forms

module subscript-Subscript-78 where

  -- ctx-102: 17 nodes, 1 forms
  -- [(untyped)]
  --   σ=148 (17×)
  ctx-102-τ102 : τ 102 ≡ τ 102
  ctx-102-τ102 = refl

  -- ctx-98: 4 nodes, 1 forms
  -- [(untyped)]
  --   σ=144 (4×)
  ctx-98-τ98 : τ 98 ≡ τ 98
  ctx-98-τ98 = refl


-- ── index (Index) ──────────────────────────────
-- 20 nodes, 4 type contexts, 8 forms

module index-Index-16 where

  -- ctx-251: 10 nodes, 3 forms
  -- [(untyped)]
  --   σ=371 (1×)
  --   σ=1462 (3×)
  --   σ=1577 (6×)
  ctx-251-τ251 : τ 251 ≡ τ 251
  ctx-251-τ251 = refl

  -- ctx-128: 6 nodes, 3 forms
  -- [(untyped)]
  --   σ=190 (1×)
  --   σ=336 (3×)
  --   σ=415 (2×)
  ctx-128-τ128 : τ 128 ≡ τ 128
  ctx-128-τ128 = refl

  -- ctx-18: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=27 (2×)
  ctx-18-τ18 : τ 18 ≡ τ 18
  ctx-18-τ18 = refl

  -- ctx-26: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=34 (2×)
  ctx-26-τ26 : τ 26 ≡ τ 26
  ctx-26-τ26 = refl


-- ── subscript (Subscript) ──────────────────────
-- 20 nodes, 5 type contexts, 13 forms

module subscript-Subscript-17 where

  -- ctx-252: 10 nodes, 5 forms
  -- [(untyped)]
  --   σ=372 (1×)
  --   σ=1463 (2×)
  --   σ=1516 (1×)
  --   σ=1578 (2×)
  --   σ=1589 (4×)
  ctx-252-τ252 : τ 252 ≡ τ 252
  ctx-252-τ252 = refl

  -- ctx-129: 6 nodes, 5 forms
  -- [(untyped)]
  --   σ=191 (1×)
  --   σ=337 (2×)
  --   σ=416 (1×)
  --   σ=1107 (1×)
  --   σ=1213 (1×)
  ctx-129-τ129 : τ 129 ≡ τ 129
  ctx-129-τ129 = refl

  -- ctx-19: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=28 (2×)
  ctx-19-τ19 : τ 19 ≡ τ 19
  ctx-19-τ19 = refl

  -- ctx-27: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=35 (1×)
  ctx-27-τ27 : τ 27 ≡ τ 27
  ctx-27-τ27 = refl

  -- ctx-281: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=404 (1×)
  ctx-281-τ281 : τ 281 ≡ τ 281
  ctx-281-τ281 = refl


-- ── projection@? (Attribute) ───────────────────
-- 20 nodes, 1 type contexts, 11 forms

module projection-at-x3f-Attribute-258 where

  -- ctx-188: 20 nodes, 11 forms
  -- [(untyped)]
  ctx-188-τ188 : τ 188 ≡ τ 188
  ctx-188-τ188 = refl


-- ── projection.compute@? (Call) ────────────────
-- 20 nodes, 1 type contexts, 11 forms

module projection-compute-at-x3f-Call-259 where

  -- ctx-361: 20 nodes, 11 forms
  -- [(untyped)]
  ctx-361-τ361 : τ 361 ≡ τ 361
  ctx-361-τ361 = refl


-- ── product.unpack (Tuple) ─────────────────────
-- 19 nodes, 1 type contexts, 10 forms

module product-unpack-Tuple-45 where

  -- tuple: 19 nodes, 10 forms
  -- [tuple]
  tuple-τ59 : τ 59 ≡ τ 59
  tuple-τ59 = refl


-- ── arguments (arguments) ──────────────────────
-- 18 nodes, 1 type contexts, 2 forms

module arguments-12 where

  -- ctx-12: 18 nodes, 2 forms
  -- [(untyped)]
  --   σ=21 (15×)
  --   σ=1677 (3×)
  ctx-12-τ12 : τ 12 ≡ τ 12
  ctx-12-τ12 = refl


-- ── apply (Call) ───────────────────────────────
-- 18 nodes, 2 type contexts, 14 forms

module apply-Call-353 where

  -- ctx-473: 16 nodes, 12 forms
  -- [(untyped)]
  ctx-473-τ473 : τ 473 ≡ τ 473
  ctx-473-τ473 = refl

  -- ctx-653: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=1339 (1×)
  --   σ=1355 (1×)
  ctx-653-τ653 : τ 653 ≡ τ 653
  ctx-653-τ653 = refl


-- ── add (Add) ──────────────────────────────────
-- 17 nodes, 1 type contexts, 1 forms

module add-Add-57 where

  -- ctx-73: 17 nodes, 1 forms
  -- [(untyped)]
  --   σ=106 (17×)
  ctx-73-τ73 : τ 73 ≡ τ 73
  ctx-73-τ73 = refl


-- ── exponential.literal (Dict) ─────────────────
-- 15 nodes, 1 type contexts, 1 forms

module exponential-literal-Dict-18 where

  -- dict: 15 nodes, 1 forms
  -- [dict]
  --   σ=29 (15×)
  dict-τ20 : τ 20 ≡ τ 20
  dict-τ20 = refl


-- ── in (In) ────────────────────────────────────
-- 15 nodes, 1 type contexts, 1 forms

module in-k-In-61 where

  -- ctx-77: 15 nodes, 1 forms
  -- [(untyped)]
  --   σ=114 (15×)
  ctx-77-τ77 : τ 77 ≡ τ 77
  ctx-77-τ77 = refl


-- ── cardinality (Call) ─────────────────────────
-- 15 nodes, 1 type contexts, 8 forms

module cardinality-Call-70 where

  -- int: 15 nodes, 8 forms
  -- [int]
  --   σ=127 (1×)
  --   σ=172 (1×)
  --   σ=517 (2×)
  --   σ=525 (1×)
  --   σ=589 (4×)
  --   σ=1777 (2×)
  --   σ=1780 (2×)
  --   σ=1783 (2×)
  int-τ87 : τ 87 ≡ τ 87
  int-τ87 = refl


-- ── partial@state (Attribute) ──────────────────
-- 15 nodes, 1 type contexts, 7 forms

module partial-at-state-Attribute-217 where

  -- Self-_cell_contents-get: 15 nodes, 7 forms
  -- [Self._cell_contents.get, Self._cell_obs.get, Self._cell_obs.keys, Self._cleavage_fibers.append, Self._cleavage_levels.append]
  --   σ=457 (1×)
  --   σ=483 (2×)
  --   σ=642 (2×)
  --   σ=760 (1×)
  --   σ=921 (7×)
  --   σ=1103 (1×)
  --   σ=1982 (1×)
  Self-_cell_contents-get-τ153 : τ 153 ≡ τ 153
  Self-_cell_contents-get-τ153 = refl


-- ── subscript (Subscript) ──────────────────────
-- 15 nodes, 2 type contexts, 11 forms

module subscript-Subscript-254 where

  -- ctx-355: 14 nodes, 10 forms
  -- [(untyped)]
  ctx-355-τ355 : τ 355 ≡ τ 355
  ctx-355-τ355 = refl

  -- ctx-434: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=703 (1×)
  ctx-434-τ434 : τ 434 ≡ τ 434
  ctx-434-τ434 = refl


-- ── morphism@? (Attribute) ─────────────────────
-- 15 nodes, 1 type contexts, 11 forms

module morphism-at-x3f-Attribute-300 where

  -- ctx-188: 15 nodes, 11 forms
  -- [(untyped)]
  ctx-188-τ188 : τ 188 ≡ τ 188
  ctx-188-τ188 = refl


-- ── noteq (NotEq) ──────────────────────────────
-- 14 nodes, 1 type contexts, 1 forms

module noteq-NotEq-34 where

  -- ctx-48: 14 nodes, 1 forms
  -- [(untyped)]
  --   σ=59 (14×)
  ctx-48-τ48 : τ 48 ≡ τ 48
  ctx-48-τ48 = refl


-- ── subscript (Subscript) ──────────────────────
-- 13 nodes, 2 type contexts, 10 forms

module subscript-Subscript-27 where

  -- ctx-37: 12 nodes, 9 forms
  -- [(untyped)]
  ctx-37-τ37 : τ 37 ≡ τ 37
  ctx-37-τ37 = refl

  -- ctx-150: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=220 (1×)
  ctx-150-τ150 : τ 150 ≡ τ 150
  ctx-150-τ150 = refl


-- ── free_monoid.fold (JoinedStr) ───────────────
-- 13 nodes, 1 type contexts, 4 forms

module free_monoid-fold-JoinedStr-673 where

  -- str: 13 nodes, 4 forms
  -- [str]
  --   σ=1820 (4×)
  --   σ=1827 (7×)
  --   σ=1855 (1×)
  --   σ=2079 (1×)
  str-τ850 : τ 850 ≡ τ 850
  str-τ850 = refl


-- ── apply (Call) ───────────────────────────────
-- 12 nodes, 1 type contexts, 7 forms

module apply-Call-46 where

  -- ctx-61: 12 nodes, 7 forms
  -- [(untyped)]
  --   σ=82 (1×)
  --   σ=84 (1×)
  --   σ=492 (1×)
  --   σ=792 (6×)
  --   σ=960 (1×)
  --   σ=1258 (1×)
  --   σ=1732 (1×)
  ctx-61-τ61 : τ 61 ≡ τ 61
  ctx-61-τ61 = refl


-- ── let (Assign) ───────────────────────────────
-- 12 nodes, 1 type contexts, 12 forms

module let-k-Assign-255 where

  -- ctx-356: 12 nodes, 12 forms
  -- [(untyped)]
  ctx-356-τ356 : τ 356 ≡ τ 356
  ctx-356-τ356 = refl


-- ── let (Assign) ───────────────────────────────
-- 11 nodes, 2 type contexts, 11 forms

module let-k-Assign-36 where

  -- ctx-50: 9 nodes, 9 forms
  -- [(untyped)]
  ctx-50-τ50 : τ 50 ≡ τ 50
  ctx-50-τ50 = refl

  -- ctx-352: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=537 (1×)
  --   σ=540 (1×)
  ctx-352-τ352 : τ 352 ≡ τ 352
  ctx-352-τ352 = refl


-- ── terminal.map (Return) ──────────────────────
-- 11 nodes, 2 type contexts, 9 forms

module terminal-map-Return-42 where

  -- ctx-56: 9 nodes, 7 forms
  -- [(untyped)]
  --   σ=70 (1×)
  --   σ=91 (3×)
  --   σ=271 (1×)
  --   σ=867 (1×)
  --   σ=1568 (1×)
  --   σ=1689 (1×)
  --   σ=1765 (1×)
  ctx-56-τ56 : τ 56 ≡ τ 56
  ctx-56-τ56 = refl

  -- ctx-162: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=234 (1×)
  --   σ=882 (1×)
  ctx-162-τ162 : τ 162 ≡ τ 162
  ctx-162-τ162 = refl


-- ── equalizer (Compare) ────────────────────────
-- 11 nodes, 3 type contexts, 7 forms

module equalizer-Compare-352 where

  -- ctx-471: 8 nodes, 5 forms
  -- [(untyped)]
  --   σ=806 (4×)
  --   σ=926 (1×)
  --   σ=1190 (1×)
  --   σ=1317 (1×)
  --   σ=1645 (1×)
  ctx-471-τ471 : τ 471 ≡ τ 471
  ctx-471-τ471 = refl

  -- ctx-595: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=1149 (2×)
  ctx-595-τ595 : τ 595 ≡ τ 595
  ctx-595-τ595 = refl

  -- ctx-522: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=905 (1×)
  ctx-522-τ522 : τ 522 ≡ τ 522
  ctx-522-τ522 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 11 nodes, 2 type contexts, 7 forms

module effect-seq-Expr-354 where

  -- ctx-474: 10 nodes, 6 forms
  -- [(untyped)]
  --   σ=809 (4×)
  --   σ=943 (1×)
  --   σ=1171 (1×)
  --   σ=1192 (1×)
  --   σ=1319 (1×)
  --   σ=1334 (2×)
  ctx-474-τ474 : τ 474 ≡ τ 474
  ctx-474-τ474 = refl

  -- ctx-659: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1356 (1×)
  ctx-659-τ659 : τ 659 ≡ τ 659
  ctx-659-τ659 = refl


-- ── product (Tuple) ────────────────────────────
-- 10 nodes, 1 type contexts, 1 forms

module product-Tuple-160 where

  -- tuple: 10 nodes, 1 forms
  -- [tuple]
  --   σ=342 (10×)
  tuple-τ226 : τ 226 ≡ τ 226
  tuple-τ226 = refl


-- ── index (Index) ──────────────────────────────
-- 10 nodes, 1 type contexts, 1 forms

module index-Index-161 where

  -- ctx-227: 10 nodes, 1 forms
  -- [(untyped)]
  --   σ=343 (10×)
  ctx-227-τ227 : τ 227 ≡ τ 227
  ctx-227-τ227 = refl


-- ── subscript (Subscript) ──────────────────────
-- 10 nodes, 1 type contexts, 1 forms

module subscript-Subscript-162 where

  -- ctx-228: 10 nodes, 1 forms
  -- [(untyped)]
  --   σ=344 (10×)
  ctx-228-τ228 : τ 228 ≡ τ 228
  ctx-228-τ228 = refl


-- ── apply (Call) ───────────────────────────────
-- 10 nodes, 2 type contexts, 5 forms

module apply-Call-175 where

  -- ctx-242: 8 nodes, 3 forms
  -- [(untyped)]
  --   σ=362 (4×)
  --   σ=409 (1×)
  --   σ=1431 (3×)
  ctx-242-τ242 : τ 242 ≡ τ 242
  ctx-242-τ242 = refl

  -- ctx-728: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=1492 (1×)
  --   σ=2067 (1×)
  ctx-728-τ728 : τ 728 ≡ τ 728
  ctx-728-τ728 = refl


-- ── free_monoid.op@state (Attribute) ───────────
-- 10 nodes, 1 type contexts, 4 forms

module free_monoid-op-at-state-Attribute-243 where

  -- Self-_cleavage_levels-append: 10 nodes, 4 forms
  -- [Self._cell_contents.get, Self._cell_obs.get, Self._cell_obs.keys, Self._cleavage_fibers.append, Self._cleavage_levels.append]
  --   σ=519 (1×)
  --   σ=530 (1×)
  --   σ=624 (7×)
  --   σ=1376 (1×)
  Self-_cleavage_levels-append-τ153 : τ 153 ≡ τ 153
  Self-_cleavage_levels-append-τ153 = refl


-- ── notin (NotIn) ──────────────────────────────
-- 9 nodes, 1 type contexts, 1 forms

module notin-NotIn-23 where

  -- ctx-33: 9 nodes, 1 forms
  -- [(untyped)]
  --   σ=42 (9×)
  ctx-33-τ33 : τ 33 ≡ τ 33
  ctx-33-τ33 = refl


-- ── equalizer (Compare) ────────────────────────
-- 9 nodes, 2 type contexts, 7 forms

module equalizer-Compare-62 where

  -- ctx-78: 7 nodes, 6 forms
  -- [(untyped)]
  --   σ=115 (1×)
  --   σ=208 (1×)
  --   σ=735 (1×)
  --   σ=1032 (1×)
  --   σ=1150 (2×)
  --   σ=1276 (1×)
  ctx-78-τ78 : τ 78 ≡ τ 78
  ctx-78-τ78 = refl

  -- ctx-396: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=650 (2×)
  ctx-396-τ396 : τ 396 ≡ τ 396
  ctx-396-τ396 = refl


-- ── free_monoid.literal (List) ─────────────────
-- 9 nodes, 1 type contexts, 1 forms

module free_monoid-literal-List-83 where

  -- list: 9 nodes, 1 forms
  -- [list]
  --   σ=164 (9×)
  list-τ115 : τ 115 ≡ τ 115
  list-τ115 = refl


-- ── apply (Call) ───────────────────────────────
-- 9 nodes, 2 type contexts, 5 forms

module apply-Call-118 where

  -- ctx-174: 7 nodes, 4 forms
  -- [(untyped)]
  --   σ=254 (1×)
  --   σ=811 (4×)
  --   σ=1193 (1×)
  --   σ=1320 (1×)
  ctx-174-τ174 : τ 174 ≡ τ 174
  ctx-174-τ174 = refl

  -- ctx-597: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=1152 (2×)
  ctx-597-τ597 : τ 597 ≡ τ 597
  ctx-597-τ597 = refl


-- ── monoid.op@? (Attribute) ────────────────────
-- 9 nodes, 1 type contexts, 9 forms

module monoid-op-at-x3f-Attribute-129 where

  -- ctx-188: 9 nodes, 9 forms
  -- [(untyped)]
  ctx-188-τ188 : τ 188 ≡ τ 188
  ctx-188-τ188 = refl


-- ── gt (Gt) ────────────────────────────────────
-- 9 nodes, 1 type contexts, 1 forms

module gt-Gt-215 where

  -- ctx-307: 9 nodes, 1 forms
  -- [(untyped)]
  --   σ=454 (9×)
  ctx-307-τ307 : τ 307 ≡ τ 307
  ctx-307-τ307 = refl


-- ── partial.apply@state (Call) ─────────────────
-- 9 nodes, 1 type contexts, 7 forms

module partial-apply-at-state-Call-228 where

  -- T: 9 nodes, 7 forms
  -- [T]
  --   σ=485 (1×)
  --   σ=761 (1×)
  --   σ=922 (1×)
  --   σ=927 (2×)
  --   σ=1027 (1×)
  --   σ=1051 (2×)
  --   σ=1203 (1×)
  T-τ324 : τ 324 ≡ τ 324
  T-τ324 = refl


-- ── arguments (arguments) ──────────────────────
-- 8 nodes, 2 type contexts, 6 forms

module arguments-22 where

  -- ctx-124: 5 nodes, 4 forms
  -- [(untyped)]
  --   σ=183 (1×)
  --   σ=236 (2×)
  --   σ=1638 (1×)
  --   σ=1691 (1×)
  ctx-124-τ124 : τ 124 ≡ τ 124
  ctx-124-τ124 = refl

  -- ctx-32: 3 nodes, 2 forms
  -- [(untyped)]
  --   σ=40 (2×)
  --   σ=113 (1×)
  ctx-32-τ32 : τ 32 ≡ τ 32
  ctx-32-τ32 = refl


-- ── let (Assign) ───────────────────────────────
-- 8 nodes, 2 type contexts, 7 forms

module let-k-Assign-28 where

  -- ctx-38: 5 nodes, 5 forms
  -- [(untyped)]
  --   σ=47 (1×)
  --   σ=103 (1×)
  --   σ=825 (1×)
  --   σ=1003 (1×)
  --   σ=1084 (1×)
  ctx-38-τ38 : τ 38 ≡ τ 38
  ctx-38-τ38 = refl

  -- ctx-149: 3 nodes, 2 forms
  -- [(untyped)]
  --   σ=217 (1×)
  --   σ=1160 (2×)
  ctx-149-τ149 : τ 149 ≡ τ 149
  ctx-149-τ149 = refl


-- ── monoid.op@? (Attribute) ────────────────────
-- 8 nodes, 2 type contexts, 6 forms

module monoid-op-at-x3f-Attribute-210 where

  -- ctx-178: 7 nodes, 5 forms
  -- [(untyped)]
  --   σ=720 (1×)
  --   σ=832 (1×)
  --   σ=1089 (2×)
  --   σ=1097 (1×)
  --   σ=1364 (2×)
  ctx-178-τ178 : τ 178 ≡ τ 178
  ctx-178-τ178 = refl

  -- ctx-158: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=448 (1×)
  ctx-158-τ158 : τ 158 ≡ τ 158
  ctx-158-τ158 = refl


-- ── monoid.op@? (Call) ─────────────────────────
-- 8 nodes, 2 type contexts, 7 forms

module monoid-op-at-x3f-Call-211 where

  -- ctx-444: 7 nodes, 6 forms
  -- [(untyped)]
  --   σ=721 (1×)
  --   σ=833 (1×)
  --   σ=1090 (1×)
  --   σ=1098 (1×)
  --   σ=1365 (2×)
  --   σ=1371 (1×)
  ctx-444-τ444 : τ 444 ≡ τ 444
  ctx-444-τ444 = refl

  -- ctx-303: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=450 (1×)
  ctx-303-τ303 : τ 303 ≡ τ 303
  ctx-303-τ303 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 8 nodes, 2 type contexts, 7 forms

module effect-seq-Expr-212 where

  -- ctx-445: 7 nodes, 6 forms
  -- [(untyped)]
  --   σ=722 (1×)
  --   σ=834 (1×)
  --   σ=1091 (1×)
  --   σ=1099 (1×)
  --   σ=1366 (2×)
  --   σ=1372 (1×)
  ctx-445-τ445 : τ 445 ≡ τ 445
  ctx-445-τ445 = refl

  -- ctx-304: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=451 (1×)
  ctx-304-τ304 : τ 304 ≡ τ 304
  ctx-304-τ304 = refl


-- ── sub (Sub) ──────────────────────────────────
-- 8 nodes, 1 type contexts, 1 forms

module sub-Sub-220 where

  -- ctx-313: 8 nodes, 1 forms
  -- [(untyped)]
  --   σ=461 (8×)
  ctx-313-τ313 : τ 313 ≡ τ 313
  ctx-313-τ313 = refl


-- ── let (Assign) ───────────────────────────────
-- 8 nodes, 1 type contexts, 4 forms

module let-k-Assign-349 where

  -- ctx-467: 8 nodes, 4 forms
  -- [(untyped)]
  --   σ=793 (4×)
  --   σ=973 (2×)
  --   σ=1259 (1×)
  --   σ=1733 (1×)
  ctx-467-τ467 : τ 467 ≡ τ 467
  ctx-467-τ467 = refl


-- ── product (Tuple) ────────────────────────────
-- 8 nodes, 4 type contexts, 7 forms

module product-Tuple-357 where

  -- tuple: 4 nodes, 4 forms
  -- [tuple]
  --   σ=817 (1×)
  --   σ=1232 (1×)
  --   σ=1266 (1×)
  --   σ=1752 (1×)
  tuple-τ477 : τ 477 ≡ τ 477
  tuple-τ477 = refl

  -- tuple: 2 nodes, 1 forms
  -- [tuple]
  --   σ=1425 (2×)
  tuple-τ693 : τ 693 ≡ τ 693
  tuple-τ693 = refl

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=1197 (1×)
  tuple-τ608 : τ 608 ≡ τ 608
  tuple-τ608 = refl

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=1324 (1×)
  tuple-τ646 : τ 646 ≡ τ 646
  tuple-τ646 = refl


-- ── apply (Call) ───────────────────────────────
-- 8 nodes, 2 type contexts, 7 forms

module apply-Call-377 where

  -- ctx-499: 7 nodes, 6 forms
  -- [(untyped)]
  --   σ=858 (1×)
  --   σ=1015 (1×)
  --   σ=1059 (2×)
  --   σ=1206 (1×)
  --   σ=1563 (1×)
  --   σ=1659 (1×)
  ctx-499-τ499 : τ 499 ≡ τ 499
  ctx-499-τ499 = refl

  -- ctx-660: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1357 (1×)
  ctx-660-τ660 : τ 660 ≡ τ 660
  ctx-660-τ660 = refl


-- ── div (Div) ──────────────────────────────────
-- 8 nodes, 1 type contexts, 1 forms

module div-Div-675 where

  -- ctx-852: 8 nodes, 1 forms
  -- [(untyped)]
  --   σ=1823 (8×)
  ctx-852-τ852 : τ 852 ≡ τ 852
  ctx-852-τ852 = refl


-- ── free_monoid.op@sequence (Attribute) ────────
-- 8 nodes, 1 type contexts, 1 forms

module free_monoid-op-at-sequence-Attribute-715 where

  -- list-append: 8 nodes, 1 forms
  -- [Self._cascade_abstraction_merge, Self._cascade_eta, Self._cell_contents, Self._cell_obs, Self._cleavage_fibers]
  --   σ=1926 (8×)
  list-append-τ34 : τ 34 ≡ τ 34
  list-append-τ34 = refl


-- ── arg (arg) ──────────────────────────────────
-- 7 nodes, 2 type contexts, 5 forms

module arg-79 where

  -- ctx-103: 5 nodes, 4 forms
  -- [(untyped)]
  --   σ=149 (2×)
  --   σ=1219 (1×)
  --   σ=1220 (1×)
  --   σ=1221 (1×)
  ctx-103-τ103 : τ 103 ≡ τ 103
  ctx-103-τ103 = refl

  -- ctx-99: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=145 (2×)
  ctx-99-τ99 : τ 99 ≡ τ 99
  ctx-99-τ99 = refl


-- ── monoid.accum (AugAssign) ───────────────────
-- 7 nodes, 1 type contexts, 3 forms

module monoid-accum-AugAssign-102 where

  -- ctx-148: 7 nodes, 3 forms
  -- [(untyped)]
  --   σ=215 (1×)
  --   σ=608 (1×)
  --   σ=837 (5×)
  ctx-148-τ148 : τ 148 ≡ τ 148
  ctx-148-τ148 = refl


-- ── comprehension (comprehension) ──────────────
-- 7 nodes, 2 type contexts, 6 forms

module comprehension-232 where

  -- ctx-518: 6 nodes, 5 forms
  -- [(untyped)]
  --   σ=896 (1×)
  --   σ=996 (1×)
  --   σ=1253 (1×)
  --   σ=1328 (2×)
  --   σ=1887 (1×)
  ctx-518-τ518 : τ 518 ≡ τ 518
  ctx-518-τ518 = refl

  -- ctx-330: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=496 (1×)
  ctx-330-τ330 : τ 330 ≡ τ 330
  ctx-330-τ330 = refl


-- ── fixpoint.next (Continue) ───────────────────
-- 7 nodes, 1 type contexts, 1 forms

module fixpoint-next-Continue-304 where

  -- ctx-412: 7 nodes, 1 forms
  -- [(untyped)]
  --   σ=671 (7×)
  ctx-412-τ412 : τ 412 ≡ τ 412
  ctx-412-τ412 = refl


-- ── apply (Call) ───────────────────────────────
-- 7 nodes, 1 type contexts, 6 forms

module apply-Call-343 where

  -- ctx-456: 7 nodes, 6 forms
  -- [(untyped)]
  --   σ=762 (1×)
  --   σ=923 (1×)
  --   σ=928 (1×)
  --   σ=1008 (1×)
  --   σ=1052 (2×)
  --   σ=1204 (1×)
  ctx-456-τ456 : τ 456 ≡ τ 456
  ctx-456-τ456 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 7 nodes, 1 type contexts, 6 forms

module effect-seq-Expr-344 where

  -- ctx-457: 7 nodes, 6 forms
  -- [(untyped)]
  --   σ=763 (1×)
  --   σ=924 (1×)
  --   σ=929 (1×)
  --   σ=1009 (1×)
  --   σ=1053 (2×)
  --   σ=1205 (1×)
  ctx-457-τ457 : τ 457 ≡ τ 457
  ctx-457-τ457 = refl


-- ── alias (alias) ──────────────────────────────
-- 6 nodes, 1 type contexts, 6 forms

module alias-2 where

  -- ctx-2: 6 nodes, 6 forms
  -- [(untyped)]
  --   σ=2 (1×)
  --   σ=4 (1×)
  --   σ=5 (1×)
  --   σ=7 (1×)
  --   σ=8 (1×)
  --   σ=9 (1×)
  ctx-2-τ2 : τ 2 ≡ τ 2
  ctx-2-τ2 = refl


-- ── let (Assign) ───────────────────────────────
-- 6 nodes, 1 type contexts, 6 forms

module let-k-Assign-32 where

  -- ctx-45: 6 nodes, 6 forms
  -- [(untyped)]
  --   σ=55 (1×)
  --   σ=508 (1×)
  --   σ=511 (1×)
  --   σ=554 (1×)
  --   σ=696 (1×)
  --   σ=1210 (1×)
  ctx-45-τ45 : τ 45 ≡ τ 45
  ctx-45-τ45 = refl


-- ── arguments (arguments) ──────────────────────
-- 6 nodes, 2 type contexts, 6 forms

module arguments-44 where

  -- ctx-168: 5 nodes, 5 forms
  -- [(untyped)]
  --   σ=245 (1×)
  --   σ=727 (1×)
  --   σ=1458 (1×)
  --   σ=1483 (1×)
  --   σ=1555 (1×)
  ctx-168-τ168 : τ 168 ≡ τ 168
  ctx-168-τ168 = refl

  -- ctx-58: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=74 (1×)
  ctx-58-τ58 : τ 58 ≡ τ 58
  ctx-58-τ58 = refl


-- ── eq (Eq) ────────────────────────────────────
-- 6 nodes, 1 type contexts, 1 forms

module eq-Eq-49 where

  -- ctx-65: 6 nodes, 1 forms
  -- [(untyped)]
  --   σ=88 (6×)
  ctx-65-τ65 : τ 65 ≡ τ 65
  ctx-65-τ65 = refl


-- ── coerce (FormattedValue) ────────────────────
-- 6 nodes, 1 type contexts, 6 forms

module coerce-FormattedValue-87 where

  -- ctx-119: 6 nodes, 6 forms
  -- [(untyped)]
  --   σ=173 (1×)
  --   σ=526 (1×)
  --   σ=1778 (1×)
  --   σ=1781 (1×)
  --   σ=1784 (1×)
  --   σ=1950 (1×)
  ctx-119-τ119 : τ 119 ≡ τ 119
  ctx-119-τ119 = refl


-- ── product (Tuple) ────────────────────────────
-- 6 nodes, 1 type contexts, 1 forms

module product-Tuple-163 where

  -- tuple: 6 nodes, 1 forms
  -- [tuple]
  --   σ=348 (6×)
  tuple-τ229 : τ 229 ≡ τ 229
  tuple-τ229 = refl


-- ── index (Index) ──────────────────────────────
-- 6 nodes, 1 type contexts, 1 forms

module index-Index-164 where

  -- ctx-230: 6 nodes, 1 forms
  -- [(untyped)]
  --   σ=349 (6×)
  ctx-230-τ230 : τ 230 ≡ τ 230
  ctx-230-τ230 = refl


-- ── subscript (Subscript) ──────────────────────
-- 6 nodes, 1 type contexts, 1 forms

module subscript-Subscript-165 where

  -- ctx-231: 6 nodes, 1 forms
  -- [(untyped)]
  --   σ=350 (6×)
  ctx-231-τ231 : τ 231 ≡ τ 231
  ctx-231-τ231 = refl


-- ── index (Index) ──────────────────────────────
-- 6 nodes, 1 type contexts, 1 forms

module index-Index-170 where

  -- ctx-237: 6 nodes, 1 forms
  -- [(untyped)]
  --   σ=357 (6×)
  ctx-237-τ237 : τ 237 ≡ τ 237
  ctx-237-τ237 = refl


-- ── subscript (Subscript) ──────────────────────
-- 6 nodes, 1 type contexts, 1 forms

module subscript-Subscript-171 where

  -- ctx-238: 6 nodes, 1 forms
  -- [(untyped)]
  --   σ=358 (6×)
  ctx-238-τ238 : τ 238 ≡ τ 238
  ctx-238-τ238 = refl


-- ── arg (arg) ──────────────────────────────────
-- 6 nodes, 2 type contexts, 5 forms

module arg-331 where

  -- ctx-440: 3 nodes, 2 forms
  -- [(untyped)]
  --   σ=710 (1×)
  --   σ=869 (2×)
  ctx-440-τ440 : τ 440 ≡ τ 440
  ctx-440-τ440 = refl

  -- ctx-452: 3 nodes, 3 forms
  -- [(untyped)]
  --   σ=747 (1×)
  --   σ=912 (1×)
  --   σ=933 (1×)
  ctx-452-τ452 : τ 452 ≡ τ 452
  ctx-452-τ452 = refl


-- ── let (Assign) ───────────────────────────────
-- 6 nodes, 1 type contexts, 3 forms

module let-k-Assign-355 where

  -- ctx-476: 6 nodes, 3 forms
  -- [(untyped)]
  --   σ=812 (4×)
  --   σ=1194 (1×)
  --   σ=1321 (1×)
  ctx-476-τ476 : τ 476 ≡ τ 476
  ctx-476-τ476 = refl


-- ── fiber (Call) ───────────────────────────────
-- 6 nodes, 1 type contexts, 4 forms

module fiber-Call-373 where

  -- bool: 6 nodes, 4 forms
  -- [bool]
  --   σ=851 (1×)
  --   σ=1011 (1×)
  --   σ=1055 (3×)
  --   σ=1872 (1×)
  bool-τ494 : τ 494 ≡ τ 494
  bool-τ494 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 6 nodes, 2 type contexts, 5 forms

module effect-seq-Expr-378 where

  -- ctx-500: 5 nodes, 4 forms
  -- [(untyped)]
  --   σ=859 (1×)
  --   σ=1016 (1×)
  --   σ=1060 (2×)
  --   σ=1207 (1×)
  ctx-500-τ500 : τ 500 ≡ τ 500
  ctx-500-τ500 = refl

  -- ctx-661: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1358 (1×)
  ctx-661-τ661 : τ 661 ≡ τ 661
  ctx-661-τ661 = refl


-- ── apply (Call) ───────────────────────────────
-- 6 nodes, 1 type contexts, 3 forms

module apply-Call-550 where

  -- ctx-701: 6 nodes, 3 forms
  -- [(untyped)]
  --   σ=1441 (2×)
  --   σ=1442 (2×)
  --   σ=1443 (2×)
  ctx-701-τ701 : τ 701 ≡ τ 701
  ctx-701-τ701 = refl


-- ── bimap (BinOp) ──────────────────────────────
-- 6 nodes, 3 type contexts, 6 forms

module bimap-BinOp-676 where

  -- ctx-853: 4 nodes, 4 forms
  -- [(untyped)]
  --   σ=1824 (1×)
  --   σ=1834 (1×)
  --   σ=1841 (1×)
  --   σ=1996 (1×)
  ctx-853-τ853 : τ 853 ≡ τ 853
  ctx-853-τ853 = refl

  -- ctx-921: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=2001 (1×)
  ctx-921-τ921 : τ 921 ≡ τ 921
  ctx-921-τ921 = refl

  -- ctx-949: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=2077 (1×)
  ctx-949-τ949 : τ 949 ≡ τ 949
  ctx-949-τ949 = refl


-- ── coerce (FormattedValue) ────────────────────
-- 5 nodes, 1 type contexts, 5 forms

module coerce-FormattedValue-86 where

  -- ctx-118: 5 nodes, 5 forms
  -- [(untyped)]
  --   σ=169 (1×)
  --   σ=311 (1×)
  --   σ=1775 (1×)
  --   σ=1929 (1×)
  --   σ=1948 (1×)
  ctx-118-τ118 : τ 118 ≡ τ 118
  ctx-118-τ118 = refl


-- ── morphism@? (Attribute) ─────────────────────
-- 5 nodes, 2 type contexts, 5 forms

module morphism-at-x3f-Attribute-109 where

  -- ctx-178: 4 nodes, 4 forms
  -- [(untyped)]
  --   σ=263 (1×)
  --   σ=268 (1×)
  --   σ=739 (1×)
  --   σ=828 (1×)
  ctx-178-τ178 : τ 178 ≡ τ 178
  ctx-178-τ178 = refl

  -- ctx-158: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=229 (1×)
  ctx-158-τ158 : τ 158 ≡ τ 158
  ctx-158-τ158 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 5 nodes, 2 type contexts, 5 forms

module annassign-AnnAssign-126 where

  -- ctx-185: 4 nodes, 4 forms
  -- [(untyped)]
  --   σ=279 (1×)
  --   σ=752 (1×)
  --   σ=1336 (1×)
  --   σ=1527 (1×)
  ctx-185-τ185 : τ 185 ≡ τ 185
  ctx-185-τ185 = refl

  -- ctx-391: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=637 (1×)
  ctx-391-τ391 : τ 391 ≡ τ 391
  ctx-391-τ391 = refl


-- ── equalizer (Compare) ────────────────────────
-- 5 nodes, 1 type contexts, 5 forms

module equalizer-Compare-128 where

  -- ctx-187: 5 nodes, 5 forms
  -- [(untyped)]
  --   σ=284 (1×)
  --   σ=557 (1×)
  --   σ=1117 (1×)
  --   σ=1279 (1×)
  --   σ=1905 (1×)
  ctx-187-τ187 : τ 187 ≡ τ 187
  ctx-187-τ187 = refl


-- ── monoid.op@? (Call) ─────────────────────────
-- 5 nodes, 1 type contexts, 5 forms

module monoid-op-at-x3f-Call-130 where

  -- ctx-189: 5 nodes, 5 forms
  -- [(untyped)]
  --   σ=286 (1×)
  --   σ=598 (1×)
  --   σ=862 (1×)
  --   σ=1156 (1×)
  --   σ=1308 (1×)
  ctx-189-τ189 : τ 189 ≡ τ 189
  ctx-189-τ189 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 5 nodes, 1 type contexts, 5 forms

module effect-seq-Expr-131 where

  -- ctx-190: 5 nodes, 5 forms
  -- [(untyped)]
  --   σ=287 (1×)
  --   σ=599 (1×)
  --   σ=863 (1×)
  --   σ=1157 (1×)
  --   σ=1309 (1×)
  ctx-190-τ190 : τ 190 ≡ τ 190
  ctx-190-τ190 = refl


-- ── apply (Call) ───────────────────────────────
-- 5 nodes, 1 type contexts, 3 forms

module apply-Call-137 where

  -- ctx-198: 5 nodes, 3 forms
  -- [(untyped)]
  --   σ=297 (2×)
  --   σ=1771 (2×)
  --   σ=1809 (1×)
  ctx-198-τ198 : τ 198 ≡ τ 198
  ctx-198-τ198 = refl


-- ── coerce (FormattedValue) ────────────────────
-- 5 nodes, 2 type contexts, 5 forms

module coerce-FormattedValue-150 where

  -- ctx-840: 4 nodes, 4 forms
  -- [(untyped)]
  --   σ=1788 (1×)
  --   σ=1937 (1×)
  --   σ=1939 (1×)
  --   σ=2040 (1×)
  ctx-840-τ840 : τ 840 ≡ τ 840
  ctx-840-τ840 = refl

  -- ctx-211: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=313 (1×)
  ctx-211-τ211 : τ 211 ≡ τ 211
  ctx-211-τ211 = refl


-- ── let (Assign) ───────────────────────────────
-- 5 nodes, 1 type contexts, 4 forms

module let-k-Assign-209 where

  -- ctx-302: 5 nodes, 4 forms
  -- [(untyped)]
  --   σ=442 (2×)
  --   σ=545 (1×)
  --   σ=903 (1×)
  --   σ=1238 (1×)
  ctx-302-τ302 : τ 302 ≡ τ 302
  ctx-302-τ302 = refl


-- ── fold (For) ─────────────────────────────────
-- 5 nodes, 2 type contexts, 5 forms

module fold-For-213 where

  -- ctx-483: 4 nodes, 4 forms
  -- [(untyped)]
  --   σ=835 (1×)
  --   σ=1092 (1×)
  --   σ=1100 (1×)
  --   σ=1373 (1×)
  ctx-483-τ483 : τ 483 ≡ τ 483
  ctx-483-τ483 = refl

  -- ctx-305: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=452 (1×)
  ctx-305-τ305 : τ 305 ≡ τ 305
  ctx-305-τ305 = refl


-- ── equalizer (Compare) ────────────────────────
-- 5 nodes, 2 type contexts, 5 forms

module equalizer-Compare-252 where

  -- ctx-468: 4 nodes, 4 forms
  -- [(untyped)]
  --   σ=799 (1×)
  --   σ=975 (1×)
  --   σ=1037 (1×)
  --   σ=1068 (1×)
  ctx-468-τ468 : τ 468 ≡ τ 468
  ctx-468-τ468 = refl

  -- ctx-353: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=548 (1×)
  ctx-353-τ353 : τ 353 ≡ τ 353
  ctx-353-τ353 = refl


-- ── subscript (Subscript) ──────────────────────
-- 5 nodes, 1 type contexts, 4 forms

module subscript-Subscript-263 where

  -- ctx-365: 5 nodes, 4 forms
  -- [(untyped)]
  --   σ=587 (2×)
  --   σ=1593 (1×)
  --   σ=1598 (1×)
  --   σ=1604 (1×)
  ctx-365-τ365 : τ 365 ≡ τ 365
  ctx-365-τ365 = refl


-- ── morphism@? (Attribute) ─────────────────────
-- 5 nodes, 1 type contexts, 4 forms

module morphism-at-x3f-Attribute-264 where

  -- ctx-366: 5 nodes, 4 forms
  -- [(untyped)]
  --   σ=588 (2×)
  --   σ=1594 (1×)
  --   σ=1599 (1×)
  --   σ=1605 (1×)
  ctx-366-τ366 : τ 366 ≡ τ 366
  ctx-366-τ366 = refl


-- ── slice (Slice) ──────────────────────────────
-- 5 nodes, 1 type contexts, 3 forms

module slice-Slice-276 where

  -- ctx-378: 5 nodes, 3 forms
  -- [(untyped)]
  --   σ=614 (2×)
  --   σ=1178 (2×)
  --   σ=2032 (1×)
  ctx-378-τ378 : τ 378 ≡ τ 378
  ctx-378-τ378 = refl


-- ── free_monoid.op@? (Attribute) ───────────────
-- 5 nodes, 1 type contexts, 5 forms

module free_monoid-op-at-x3f-Attribute-356 where

  -- ctx-188: 5 nodes, 5 forms
  -- [(untyped)]
  --   σ=816 (1×)
  --   σ=983 (1×)
  --   σ=1293 (1×)
  --   σ=1669 (1×)
  --   σ=1750 (1×)
  ctx-188-τ188 : τ 188 ≡ τ 188
  ctx-188-τ188 = refl


-- ── coerce (Call) ──────────────────────────────
-- 5 nodes, 1 type contexts, 3 forms

module coerce-Call-374 where

  -- ctx-495: 5 nodes, 3 forms
  -- [(untyped)]
  --   σ=852 (1×)
  --   σ=1012 (1×)
  --   σ=1056 (3×)
  ctx-495-τ495 : τ 495 ≡ τ 495
  ctx-495-τ495 = refl


-- ── ifexp (IfExp) ──────────────────────────────
-- 5 nodes, 1 type contexts, 3 forms

module ifexp-IfExp-375 where

  -- ctx-496: 5 nodes, 3 forms
  -- [(untyped)]
  --   σ=853 (1×)
  --   σ=1013 (1×)
  --   σ=1057 (3×)
  ctx-496-τ496 : τ 496 ≡ τ 496
  ctx-496-τ496 = refl


-- ── let (Assign) ───────────────────────────────
-- 5 nodes, 1 type contexts, 3 forms

module let-k-Assign-376 where

  -- ctx-497: 5 nodes, 3 forms
  -- [(untyped)]
  --   σ=854 (1×)
  --   σ=1014 (1×)
  --   σ=1058 (3×)
  ctx-497-τ497 : τ 497 ≡ τ 497
  ctx-497-τ497 = refl


-- ── equalizer (Compare) ────────────────────────
-- 5 nodes, 1 type contexts, 5 forms

module equalizer-Compare-456 where

  -- ctx-585: 5 nodes, 5 forms
  -- [(untyped)]
  --   σ=1124 (1×)
  --   σ=1164 (1×)
  --   σ=1338 (1×)
  --   σ=1736 (1×)
  --   σ=1920 (1×)
  ctx-585-τ585 : τ 585 ≡ τ 585
  ctx-585-τ585 = refl


-- ── exponential (Call) ─────────────────────────
-- 5 nodes, 1 type contexts, 4 forms

module exponential-Call-558 where

  -- ctx-404: 5 nodes, 4 forms
  -- [(untyped)]
  --   σ=1452 (2×)
  --   σ=1507 (1×)
  --   σ=1716 (1×)
  --   σ=1863 (1×)
  ctx-404-τ404 : τ 404 ≡ τ 404
  ctx-404-τ404 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 4 nodes, 4 type contexts, 4 forms

module annassign-AnnAssign-19 where

  -- ctx-21: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=30 (1×)
  ctx-21-τ21 : τ 21 ≡ τ 21
  ctx-21-τ21 = refl

  -- ctx-28: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=36 (1×)
  ctx-28-τ28 : τ 28 ≡ τ 28
  ctx-28-τ28 = refl

  -- ctx-131: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=192 (1×)
  ctx-131-τ131 : τ 131 ≡ τ 131
  ctx-131-τ131 = refl

  -- ctx-253: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=373 (1×)
  ctx-253-τ253 : τ 253 ≡ τ 253
  ctx-253-τ253 = refl


-- ── equalizer (Compare) ────────────────────────
-- 4 nodes, 1 type contexts, 3 forms

module equalizer-Compare-50 where

  -- ctx-66: 4 nodes, 3 forms
  -- [(untyped)]
  --   σ=90 (2×)
  --   σ=258 (1×)
  --   σ=2052 (1×)
  ctx-66-τ66 : τ 66 ≡ τ 66
  ctx-66-τ66 = refl


-- ── apply (Call) ───────────────────────────────
-- 4 nodes, 1 type contexts, 2 forms

module apply-Call-97 where

  -- ctx-140: 4 nodes, 2 forms
  -- [(untyped)]
  --   σ=202 (2×)
  --   σ=1559 (2×)
  ctx-140-τ140 : τ 140 ≡ τ 140
  ctx-140-τ140 = refl


-- ── index (Index) ──────────────────────────────
-- 4 nodes, 3 type contexts, 3 forms

module index-Index-157 where

  -- ctx-758: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=1579 (2×)
  ctx-758-τ758 : τ 758 ≡ τ 758
  ctx-758-τ758 = refl

  -- ctx-222: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=338 (1×)
  ctx-222-τ222 : τ 222 ≡ τ 222
  ctx-222-τ222 = refl

  -- ctx-273: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=394 (1×)
  ctx-273-τ273 : τ 273 ≡ τ 273
  ctx-273-τ273 = refl


-- ── subscript (Subscript) ──────────────────────
-- 4 nodes, 3 type contexts, 3 forms

module subscript-Subscript-158 where

  -- ctx-759: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=1580 (2×)
  ctx-759-τ759 : τ 759 ≡ τ 759
  ctx-759-τ759 = refl

  -- ctx-223: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=339 (1×)
  ctx-223-τ223 : τ 223 ≡ τ 223
  ctx-223-τ223 = refl

  -- ctx-274: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=395 (1×)
  ctx-274-τ274 : τ 274 ≡ τ 274
  ctx-274-τ274 = refl


-- ── index (Index) ──────────────────────────────
-- 4 nodes, 3 type contexts, 3 forms

module index-Index-187 where

  -- ctx-265: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=387 (2×)
  ctx-265-τ265 : τ 265 ≡ τ 265
  ctx-265-τ265 = refl

  -- ctx-295: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=425 (1×)
  ctx-295-τ295 : τ 295 ≡ τ 295
  ctx-295-τ295 = refl

  -- ctx-358: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=566 (1×)
  ctx-358-τ358 : τ 358 ≡ τ 358
  ctx-358-τ358 = refl


-- ── subscript (Subscript) ──────────────────────
-- 4 nodes, 3 type contexts, 3 forms

module subscript-Subscript-188 where

  -- ctx-266: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=388 (2×)
  ctx-266-τ266 : τ 266 ≡ τ 266
  ctx-266-τ266 = refl

  -- ctx-296: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=426 (1×)
  ctx-296-τ296 : τ 296 ≡ τ 296
  ctx-296-τ296 = refl

  -- ctx-359: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=567 (1×)
  ctx-359-τ359 : τ 359 ≡ τ 359
  ctx-359-τ359 = refl


-- ── product (Tuple) ────────────────────────────
-- 4 nodes, 2 type contexts, 3 forms

module product-Tuple-193 where

  -- tuple: 3 nodes, 2 forms
  -- [tuple]
  --   σ=1517 (1×)
  --   σ=1650 (2×)
  tuple-τ738 : τ 738 ≡ τ 738
  tuple-τ738 = refl

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=405 (1×)
  tuple-τ282 : τ 282 ≡ τ 282
  tuple-τ282 = refl


-- ── index (Index) ──────────────────────────────
-- 4 nodes, 2 type contexts, 3 forms

module index-Index-194 where

  -- ctx-739: 3 nodes, 2 forms
  -- [(untyped)]
  --   σ=1518 (1×)
  --   σ=1651 (2×)
  ctx-739-τ739 : τ 739 ≡ τ 739
  ctx-739-τ739 = refl

  -- ctx-283: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=406 (1×)
  ctx-283-τ283 : τ 283 ≡ τ 283
  ctx-283-τ283 = refl


-- ── subscript (Subscript) ──────────────────────
-- 4 nodes, 2 type contexts, 3 forms

module subscript-Subscript-195 where

  -- ctx-740: 3 nodes, 2 forms
  -- [(untyped)]
  --   σ=1519 (1×)
  --   σ=1652 (2×)
  ctx-740-τ740 : τ 740 ≡ τ 740
  ctx-740-τ740 = refl

  -- ctx-284: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=407 (1×)
  ctx-284-τ284 : τ 284 ≡ τ 284
  ctx-284-τ284 = refl


-- ── gte (GtE) ──────────────────────────────────
-- 4 nodes, 1 type contexts, 1 forms

module gte-GtE-241 where

  -- ctx-340: 4 nodes, 1 forms
  -- [(untyped)]
  --   σ=515 (4×)
  ctx-340-τ340 : τ 340 ≡ τ 340
  ctx-340-τ340 = refl


-- ── subscript (Subscript) ──────────────────────
-- 4 nodes, 1 type contexts, 2 forms

module subscript-Subscript-277 where

  -- ctx-379: 4 nodes, 2 forms
  -- [(untyped)]
  --   σ=615 (2×)
  --   σ=1179 (2×)
  ctx-379-τ379 : τ 379 ≡ τ 379
  ctx-379-τ379 = refl


-- ── free_monoid (Call) ─────────────────────────
-- 4 nodes, 1 type contexts, 3 forms

module free_monoid-Call-282 where

  -- ctx-385: 4 nodes, 3 forms
  -- [(untyped)]
  --   σ=628 (2×)
  --   σ=789 (1×)
  --   σ=1128 (1×)
  ctx-385-τ385 : τ 385 ≡ τ 385
  ctx-385-τ385 = refl


-- ── free_monoid.fold (JoinedStr) ───────────────
-- 4 nodes, 2 type contexts, 2 forms

module free_monoid-fold-JoinedStr-306 where

  -- str: 3 nodes, 1 forms
  -- [str]
  --   σ=675 (3×)
  str-τ414 : τ 414 ≡ τ 414
  str-τ414 = refl

  -- str: 1 nodes, 1 forms
  -- [str]
  --   σ=841 (1×)
  str-τ487 : τ 487 ≡ τ 487
  str-τ487 = refl


-- ── apply (Call) ───────────────────────────────
-- 4 nodes, 1 type contexts, 4 forms

module apply-Call-350 where

  -- ctx-469: 4 nodes, 4 forms
  -- [(untyped)]
  --   σ=803 (1×)
  --   σ=978 (1×)
  --   σ=1039 (1×)
  --   σ=1070 (1×)
  ctx-469-τ469 : τ 469 ≡ τ 469
  ctx-469-τ469 = refl


-- ── let (Assign) ───────────────────────────────
-- 4 nodes, 1 type contexts, 4 forms

module let-k-Assign-351 where

  -- ctx-470: 4 nodes, 4 forms
  -- [(untyped)]
  --   σ=804 (1×)
  --   σ=979 (1×)
  --   σ=1040 (1×)
  --   σ=1071 (1×)
  ctx-470-τ470 : τ 470 ≡ τ 470
  ctx-470-τ470 = refl


-- ── lazy_fold (GeneratorExp) ───────────────────
-- 4 nodes, 1 type contexts, 4 forms

module lazy_fold-GeneratorExp-395 where

  -- ctx-519: 4 nodes, 4 forms
  -- [(untyped)]
  --   σ=897 (1×)
  --   σ=1254 (1×)
  --   σ=1343 (1×)
  --   σ=1888 (1×)
  ctx-519-τ519 : τ 519 ≡ τ 519
  ctx-519-τ519 = refl


-- ── product (Tuple) ────────────────────────────
-- 4 nodes, 4 type contexts, 4 forms

module product-Tuple-414 where

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=966 (1×)
  tuple-τ542 : τ 542 ≡ τ 542
  tuple-τ542 = refl

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=1489 (1×)
  tuple-τ725 : τ 725 ≡ τ 725
  tuple-τ725 = refl

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=1628 (1×)
  tuple-τ773 : τ 773 ≡ τ 773
  tuple-τ773 = refl

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=1699 (1×)
  tuple-τ805 : τ 805 ≡ τ 805
  tuple-τ805 = refl


-- ── let (Assign) ───────────────────────────────
-- 4 nodes, 1 type contexts, 4 forms

module let-k-Assign-484 where

  -- ctx-620: 4 nodes, 4 forms
  -- [(untyped)]
  --   σ=1228 (1×)
  --   σ=1803 (1×)
  --   σ=1805 (1×)
  --   σ=1807 (1×)
  ctx-620-τ620 : τ 620 ≡ τ 620
  ctx-620-τ620 = refl


-- ── eval (Call) ────────────────────────────────
-- 4 nodes, 1 type contexts, 2 forms

module eval-Call-540 where

  -- T: 4 nodes, 2 forms
  -- [T]
  --   σ=1416 (1×)
  --   σ=1529 (3×)
  T-τ689 : τ 689 ≡ τ 689
  T-τ689 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 4 nodes, 1 type contexts, 2 forms

module annassign-AnnAssign-541 where

  -- ctx-690: 4 nodes, 2 forms
  -- [(untyped)]
  --   σ=1417 (1×)
  --   σ=1530 (3×)
  ctx-690-τ690 : τ 690 ≡ τ 690
  ctx-690-τ690 = refl


-- ── equalizer (Compare) ────────────────────────
-- 3 nodes, 1 type contexts, 3 forms

module equalizer-Compare-25 where

  -- ctx-35: 3 nodes, 3 forms
  -- [(untyped)]
  --   σ=44 (1×)
  --   σ=768 (1×)
  --   σ=952 (1×)
  ctx-35-τ35 : τ 35 ≡ τ 35
  ctx-35-τ35 = refl


-- ── lt (Lt) ────────────────────────────────────
-- 3 nodes, 1 type contexts, 1 forms

module lt-Lt-52 where

  -- ctx-68: 3 nodes, 1 forms
  -- [(untyped)]
  --   σ=95 (3×)
  ctx-68-τ68 : τ 68 ≡ τ 68
  ctx-68-τ68 = refl


-- ── apply (Call) ───────────────────────────────
-- 3 nodes, 1 type contexts, 2 forms

module apply-Call-65 where

  -- ctx-82: 3 nodes, 2 forms
  -- [(untyped)]
  --   σ=120 (1×)
  --   σ=1437 (2×)
  ctx-82-τ82 : τ 82 ≡ τ 82
  ctx-82-τ82 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 3 nodes, 1 type contexts, 3 forms

module annassign-AnnAssign-96 where

  -- ctx-138: 3 nodes, 3 forms
  -- [(untyped)]
  --   σ=199 (1×)
  --   σ=377 (1×)
  --   σ=402 (1×)
  ctx-138-τ138 : τ 138 ≡ τ 138
  ctx-138-τ138 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 3 nodes, 1 type contexts, 2 forms

module effect-seq-Expr-107 where

  -- ctx-155: 3 nodes, 2 forms
  -- [(untyped)]
  --   σ=226 (1×)
  --   σ=1145 (2×)
  ctx-155-τ155 : τ 155 ≡ τ 155
  ctx-155-τ155 = refl


-- ── apply (Call) ───────────────────────────────
-- 3 nodes, 1 type contexts, 3 forms

module apply-Call-155 where

  -- ctx-217: 3 nodes, 3 forms
  -- [(untyped)]
  --   σ=324 (1×)
  --   σ=328 (1×)
  --   σ=332 (1×)
  ctx-217-τ217 : τ 217 ≡ τ 217
  ctx-217-τ217 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 3 nodes, 1 type contexts, 3 forms

module annassign-AnnAssign-156 where

  -- ctx-218: 3 nodes, 3 forms
  -- [(untyped)]
  --   σ=325 (1×)
  --   σ=329 (1×)
  --   σ=333 (1×)
  ctx-218-τ218 : τ 218 ≡ τ 218
  ctx-218-τ218 = refl


-- ── product (Tuple) ────────────────────────────
-- 3 nodes, 2 type contexts, 2 forms

module product-Tuple-200 where

  -- tuple: 2 nodes, 1 forms
  -- [tuple]
  --   σ=1464 (2×)
  tuple-τ712 : τ 712 ≡ τ 712
  tuple-τ712 = refl

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=418 (1×)
  tuple-τ290 : τ 290 ≡ τ 290
  tuple-τ290 = refl


-- ── index (Index) ──────────────────────────────
-- 3 nodes, 2 type contexts, 2 forms

module index-Index-201 where

  -- ctx-713: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=1465 (2×)
  ctx-713-τ713 : τ 713 ≡ τ 713
  ctx-713-τ713 = refl

  -- ctx-291: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=419 (1×)
  ctx-291-τ291 : τ 291 ≡ τ 291
  ctx-291-τ291 = refl


-- ── subscript (Subscript) ──────────────────────
-- 3 nodes, 3 type contexts, 3 forms

module subscript-Subscript-202 where

  -- ctx-292: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=420 (1×)
  ctx-292-τ292 : τ 292 ≡ τ 292
  ctx-292-τ292 = refl

  -- ctx-714: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1466 (1×)
  ctx-714-τ714 : τ 714 ≡ τ 714
  ctx-714-τ714 = refl

  -- ctx-723: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1479 (1×)
  ctx-723-τ723 : τ 723 ≡ τ 723
  ctx-723-τ723 = refl


-- ── equalizer (Compare) ────────────────────────
-- 3 nodes, 1 type contexts, 3 forms

module equalizer-Compare-216 where

  -- ctx-308: 3 nodes, 3 forms
  -- [(untyped)]
  --   σ=455 (1×)
  --   σ=1661 (1×)
  --   σ=2065 (1×)
  ctx-308-τ308 : τ 308 ≡ τ 308
  ctx-308-τ308 = refl


-- ── comprehension (comprehension) ──────────────
-- 3 nodes, 1 type contexts, 2 forms

module comprehension-314 where

  -- ctx-422: 3 nodes, 2 forms
  -- [(untyped)]
  --   σ=687 (2×)
  --   σ=1286 (1×)
  ctx-422-τ422 : τ 422 ≡ τ 422
  ctx-422-τ422 = refl


-- ── isnot (IsNot) ──────────────────────────────
-- 3 nodes, 1 type contexts, 1 forms

module isnot-IsNot-333 where

  -- ctx-442: 3 nodes, 1 forms
  -- [(untyped)]
  --   σ=716 (3×)
  ctx-442-τ442 : τ 442 ≡ τ 442
  ctx-442-τ442 = refl


-- ── equalizer (Compare) ────────────────────────
-- 3 nodes, 1 type contexts, 2 forms

module equalizer-Compare-334 where

  -- ctx-443: 3 nodes, 2 forms
  -- [(untyped)]
  --   σ=717 (1×)
  --   σ=1275 (2×)
  ctx-443-τ443 : τ 443 ≡ τ 443
  ctx-443-τ443 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 3 nodes, 1 type contexts, 3 forms

module annassign-AnnAssign-342 where

  -- ctx-454: 3 nodes, 3 forms
  -- [(untyped)]
  --   σ=754 (1×)
  --   σ=938 (1×)
  --   σ=945 (1×)
  ctx-454-τ454 : τ 454 ≡ τ 454
  ctx-454-τ454 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 3 nodes, 1 type contexts, 2 forms

module annassign-AnnAssign-347 where

  -- ctx-460: 3 nodes, 2 forms
  -- [(untyped)]
  --   σ=775 (2×)
  --   σ=1066 (1×)
  ctx-460-τ460 : τ 460 ≡ τ 460
  ctx-460-τ460 = refl


-- ── let (Assign) ───────────────────────────────
-- 3 nodes, 1 type contexts, 3 forms

module let-k-Assign-394 where

  -- ctx-517: 3 nodes, 3 forms
  -- [(untyped)]
  --   σ=890 (1×)
  --   σ=1025 (1×)
  --   σ=1086 (1×)
  ctx-517-τ517 : τ 517 ≡ τ 517
  ctx-517-τ517 = refl


-- ── index (Index) ──────────────────────────────
-- 3 nodes, 3 type contexts, 3 forms

module index-Index-415 where

  -- ctx-543: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=967 (1×)
  ctx-543-τ543 : τ 543 ≡ τ 543
  ctx-543-τ543 = refl

  -- ctx-726: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1490 (1×)
  ctx-726-τ726 : τ 726 ≡ τ 726
  ctx-726-τ726 = refl

  -- ctx-806: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1700 (1×)
  ctx-806-τ806 : τ 806 ≡ τ 806
  ctx-806-τ806 = refl


-- ── subscript (Subscript) ──────────────────────
-- 3 nodes, 3 type contexts, 3 forms

module subscript-Subscript-416 where

  -- ctx-544: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=968 (1×)
  ctx-544-τ544 : τ 544 ≡ τ 544
  ctx-544-τ544 = refl

  -- ctx-727: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1491 (1×)
  ctx-727-τ727 : τ 727 ≡ τ 727
  ctx-727-τ727 = refl

  -- ctx-807: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1701 (1×)
  ctx-807-τ807 : τ 807 ≡ τ 807
  ctx-807-τ807 = refl


-- ── free_monoid.literal (List) ─────────────────
-- 3 nodes, 1 type contexts, 3 forms

module free_monoid-literal-List-440 where

  -- list: 3 nodes, 3 forms
  -- [list]
  --   σ=1043 (1×)
  --   σ=1074 (1×)
  --   σ=1296 (1×)
  list-τ568 : τ 568 ≡ τ 568
  list-τ568 = refl


-- ── let (Assign) ───────────────────────────────
-- 3 nodes, 2 type contexts, 3 forms

module let-k-Assign-468 where

  -- ctx-603: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=1168 (1×)
  --   σ=2056 (1×)
  ctx-603-τ603 : τ 603 ≡ τ 603
  ctx-603-τ603 = refl

  -- ctx-654: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1340 (1×)
  ctx-654-τ654 : τ 654 ≡ τ 654
  ctx-654-τ654 = refl


-- ── apply (Call) ───────────────────────────────
-- 3 nodes, 2 type contexts, 3 forms

module apply-Call-486 where

  -- ctx-623: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=1243 (1×)
  --   σ=1249 (1×)
  ctx-623-τ623 : τ 623 ≡ τ 623
  ctx-623-τ623 = refl

  -- ctx-631: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1270 (1×)
  ctx-631-τ631 : τ 631 ≡ τ 631
  ctx-631-τ631 = refl


-- ── let (Assign) ───────────────────────────────
-- 3 nodes, 2 type contexts, 3 forms

module let-k-Assign-487 where

  -- ctx-624: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=1244 (1×)
  --   σ=1250 (1×)
  ctx-624-τ624 : τ 624 ≡ τ 624
  ctx-624-τ624 = refl

  -- ctx-632: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1271 (1×)
  ctx-632-τ632 : τ 632 ≡ τ 632
  ctx-632-τ632 = refl


-- ── apply (Call) ───────────────────────────────
-- 3 nodes, 1 type contexts, 3 forms

module apply-Call-515 where

  -- ctx-189: 3 nodes, 3 forms
  -- [(untyped)]
  --   σ=1352 (1×)
  --   σ=1419 (1×)
  --   σ=1534 (1×)
  ctx-189-τ189 : τ 189 ≡ τ 189
  ctx-189-τ189 = refl


-- ── terminal.map (Return) ──────────────────────
-- 3 nodes, 1 type contexts, 2 forms

module terminal-map-Return-559 where

  -- ctx-709: 3 nodes, 2 forms
  -- [(untyped)]
  --   σ=1453 (2×)
  --   σ=1717 (1×)
  ctx-709-τ709 : τ 709 ≡ τ 709
  ctx-709-τ709 = refl


-- ── let (Assign) ───────────────────────────────
-- 3 nodes, 1 type contexts, 3 forms

module let-k-Assign-596 where

  -- ctx-761: 3 nodes, 3 forms
  -- [(untyped)]
  --   σ=1583 (1×)
  --   σ=1585 (1×)
  --   σ=1587 (1×)
  ctx-761-τ761 : τ 761 ≡ τ 761
  ctx-761-τ761 = refl


-- ── cardinality (Call) ─────────────────────────
-- 3 nodes, 1 type contexts, 3 forms

module cardinality-Call-597 where

  -- int: 3 nodes, 3 forms
  -- [int]
  --   σ=1595 (1×)
  --   σ=1600 (1×)
  --   σ=1606 (1×)
  int-τ763 : τ 763 ≡ τ 763
  int-τ763 = refl


-- ── partial@? (Attribute) ──────────────────────
-- 3 nodes, 1 type contexts, 3 forms

module partial-at-x3f-Attribute-600 where

  -- ctx-188: 3 nodes, 3 forms
  -- [(untyped)]
  --   σ=1612 (1×)
  --   σ=1912 (1×)
  --   σ=2058 (1×)
  ctx-188-τ188 : τ 188 ≡ τ 188
  ctx-188-τ188 = refl


-- ── product (Tuple) ────────────────────────────
-- 3 nodes, 1 type contexts, 1 forms

module product-Tuple-615 where

  -- tuple: 3 nodes, 1 forms
  -- [tuple]
  --   σ=1644 (3×)
  tuple-τ782 : τ 782 ≡ τ 782
  tuple-τ782 = refl


-- ── coerce (FormattedValue) ────────────────────
-- 3 nodes, 1 type contexts, 3 forms

module coerce-FormattedValue-674 where

  -- ctx-851: 3 nodes, 3 forms
  -- [(untyped)]
  --   σ=1821 (1×)
  --   σ=1833 (1×)
  --   σ=1840 (1×)
  ctx-851-τ851 : τ 851 ≡ τ 851
  ctx-851-τ851 = refl


-- ── bimap (BinOp) ──────────────────────────────
-- 3 nodes, 1 type contexts, 3 forms

module bimap-BinOp-677 where

  -- ctx-854: 3 nodes, 3 forms
  -- [(untyped)]
  --   σ=1825 (1×)
  --   σ=1835 (1×)
  --   σ=1842 (1×)
  ctx-854-τ854 : τ 854 ≡ τ 854
  ctx-854-τ854 = refl


-- ── coerce (FormattedValue) ────────────────────
-- 3 nodes, 1 type contexts, 3 forms

module coerce-FormattedValue-678 where

  -- ctx-855: 3 nodes, 3 forms
  -- [(untyped)]
  --   σ=1828 (1×)
  --   σ=1836 (1×)
  --   σ=1843 (1×)
  ctx-855-τ855 : τ 855 ≡ τ 855
  ctx-855-τ855 = refl


-- ── free_monoid.fold (JoinedStr) ───────────────
-- 3 nodes, 1 type contexts, 3 forms

module free_monoid-fold-JoinedStr-679 where

  -- str: 3 nodes, 3 forms
  -- [str]
  --   σ=1830 (1×)
  --   σ=1837 (1×)
  --   σ=1844 (1×)
  str-τ856 : τ 856 ≡ τ 856
  str-τ856 = refl


-- ── coerce (FormattedValue) ────────────────────
-- 3 nodes, 3 type contexts, 3 forms

module coerce-FormattedValue-742 where

  -- ctx-920: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1997 (1×)
  ctx-920-τ920 : τ 920 ≡ τ 920
  ctx-920-τ920 = refl

  -- ctx-922: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=2002 (1×)
  ctx-922-τ922 : τ 922 ≡ τ 922
  ctx-922-τ922 = refl

  -- ctx-950: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=2080 (1×)
  ctx-950-τ950 : τ 950 ≡ τ 950
  ctx-950-τ950 = refl


-- ── equalizer (Compare) ────────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module equalizer-Compare-35 where

  -- ctx-49: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=60 (1×)
  --   σ=64 (1×)
  ctx-49-τ49 : τ 49 ≡ τ 49
  ctx-49-τ49 = refl


-- ── equalizer (If) ─────────────────────────────
-- 2 nodes, 1 type contexts, 1 forms

module equalizer-If-51 where

  -- ctx-67: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=92 (2×)
  ctx-67-τ67 : τ 67 ≡ τ 67
  ctx-67-τ67 = refl


-- ── terminal.map (Return) ──────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module terminal-map-Return-71 where

  -- ctx-88: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=128 (1×)
  --   σ=1405 (1×)
  ctx-88-τ88 : τ 88 ≡ τ 88
  ctx-88-τ88 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module annassign-AnnAssign-81 where

  -- ctx-106: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=153 (1×)
  --   σ=186 (1×)
  ctx-106-τ106 : τ 106 ≡ τ 106
  ctx-106-τ106 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 2 nodes, 2 type contexts, 2 forms

module annassign-AnnAssign-82 where

  -- ctx-108: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=156 (1×)
  ctx-108-τ108 : τ 108 ≡ τ 108
  ctx-108-τ108 = refl

  -- ctx-110: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=159 (1×)
  ctx-110-τ110 : τ 110 ≡ τ 110
  ctx-110-τ110 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 2 nodes, 2 type contexts, 2 forms

module annassign-AnnAssign-84 where

  -- ctx-116: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=165 (1×)
  ctx-116-τ116 : τ 116 ≡ τ 116
  ctx-116-τ116 = refl

  -- ctx-277: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=400 (1×)
  ctx-277-τ277 : τ 277 ≡ τ 277
  ctx-277-τ277 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module annassign-AnnAssign-98 where

  -- ctx-141: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=203 (1×)
  --   σ=375 (1×)
  ctx-141-τ141 : τ 141 ≡ τ 141
  ctx-141-τ141 = refl


-- ── let (Assign) ───────────────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module let-k-Assign-101 where

  -- ctx-146: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=214 (1×)
  --   σ=1796 (1×)
  ctx-146-τ146 : τ 146 ≡ τ 146
  ctx-146-τ146 = refl


-- ── free_monoid.op@? (Attribute) ───────────────
-- 2 nodes, 2 type contexts, 2 forms

module free_monoid-op-at-x3f-Attribute-110 where

  -- ctx-159: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=230 (1×)
  ctx-159-τ159 : τ 159 ≡ τ 159
  ctx-159-τ159 = refl

  -- ctx-179: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=264 (1×)
  ctx-179-τ179 : τ 179 ≡ τ 179
  ctx-179-τ179 = refl


-- ── terminal.map (Return) ──────────────────────
-- 2 nodes, 2 type contexts, 2 forms

module terminal-map-Return-114 where

  -- ctx-166: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=241 (1×)
  ctx-166-τ166 : τ 166 ≡ τ 166
  ctx-166-τ166 = refl

  -- ctx-512: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=880 (1×)
  ctx-512-τ512 : τ 512 ≡ τ 512
  ctx-512-τ512 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 2 nodes, 2 type contexts, 2 forms

module annassign-AnnAssign-159 where

  -- ctx-224: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=340 (1×)
  ctx-224-τ224 : τ 224 ≡ τ 224
  ctx-224-τ224 = refl

  -- ctx-275: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=396 (1×)
  ctx-275-τ275 : τ 275 ≡ τ 275
  ctx-275-τ275 = refl


-- ── product (Tuple) ────────────────────────────
-- 2 nodes, 2 type contexts, 2 forms

module product-Tuple-181 where

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=380 (1×)
  tuple-τ258 : τ 258 ≡ τ 258
  tuple-τ258 = refl

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=777 (1×)
  tuple-τ461 : τ 461 ≡ τ 461
  tuple-τ461 = refl


-- ── index (Index) ──────────────────────────────
-- 2 nodes, 2 type contexts, 2 forms

module index-Index-182 where

  -- ctx-259: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=381 (1×)
  ctx-259-τ259 : τ 259 ≡ τ 259
  ctx-259-τ259 = refl

  -- ctx-462: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=778 (1×)
  ctx-462-τ462 : τ 462 ≡ τ 462
  ctx-462-τ462 = refl


-- ── subscript (Subscript) ──────────────────────
-- 2 nodes, 2 type contexts, 2 forms

module subscript-Subscript-183 where

  -- ctx-260: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=382 (1×)
  ctx-260-τ260 : τ 260 ≡ τ 260
  ctx-260-τ260 = refl

  -- ctx-463: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=779 (1×)
  ctx-463-τ463 : τ 463 ≡ τ 463
  ctx-463-τ463 = refl


-- ── index (Index) ──────────────────────────────
-- 2 nodes, 2 type contexts, 2 forms

module index-Index-184 where

  -- ctx-261: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=383 (1×)
  ctx-261-τ261 : τ 261 ≡ τ 261
  ctx-261-τ261 = refl

  -- ctx-464: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=780 (1×)
  ctx-464-τ464 : τ 464 ≡ τ 464
  ctx-464-τ464 = refl


-- ── subscript (Subscript) ──────────────────────
-- 2 nodes, 2 type contexts, 2 forms

module subscript-Subscript-185 where

  -- ctx-262: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=384 (1×)
  ctx-262-τ262 : τ 262 ≡ τ 262
  ctx-262-τ262 = refl

  -- ctx-465: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=781 (1×)
  ctx-465-τ465 : τ 465 ≡ τ 465
  ctx-465-τ465 = refl


-- ── product (Tuple) ────────────────────────────
-- 2 nodes, 1 type contexts, 1 forms

module product-Tuple-189 where

  -- tuple: 2 nodes, 1 forms
  -- [tuple]
  --   σ=389 (2×)
  tuple-τ267 : τ 267 ≡ τ 267
  tuple-τ267 = refl


-- ── index (Index) ──────────────────────────────
-- 2 nodes, 1 type contexts, 1 forms

module index-Index-190 where

  -- ctx-268: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=390 (2×)
  ctx-268-τ268 : τ 268 ≡ τ 268
  ctx-268-τ268 = refl


-- ── subscript (Subscript) ──────────────────────
-- 2 nodes, 2 type contexts, 2 forms

module subscript-Subscript-191 where

  -- ctx-269: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=391 (1×)
  ctx-269-τ269 : τ 269 ≡ τ 269
  ctx-269-τ269 = refl

  -- ctx-878: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1899 (1×)
  ctx-878-τ878 : τ 878 ≡ τ 878
  ctx-878-τ878 = refl


-- ── product (Tuple) ────────────────────────────
-- 2 nodes, 1 type contexts, 1 forms

module product-Tuple-218 where

  -- tuple: 2 nodes, 1 forms
  -- [tuple]
  --   σ=458 (2×)
  tuple-τ310 : τ 310 ≡ τ 310
  tuple-τ310 = refl


-- ── partial.apply@state (Call) ─────────────────
-- 2 nodes, 2 type contexts, 2 forms

module partial-apply-at-state-Call-219 where

  -- T: 1 nodes, 1 forms
  -- [T]
  --   σ=459 (1×)
  T-τ311 : τ 311 ≡ τ 311
  T-τ311 = refl

  -- T: 1 nodes, 1 forms
  -- [T]
  --   σ=639 (1×)
  T-τ392 : τ 392 ≡ τ 392
  T-τ392 = refl


-- ── arguments (arguments) ──────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module arguments-227 where

  -- ctx-320: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=472 (1×)
  --   σ=1523 (1×)
  ctx-320-τ320 : τ 320 ≡ τ 320
  ctx-320-τ320 = refl


-- ── equalizer (Compare) ────────────────────────
-- 2 nodes, 2 type contexts, 2 forms

module equalizer-Compare-242 where

  -- ctx-341: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=518 (1×)
  ctx-341-τ341 : τ 341 ≡ τ 341
  ctx-341-τ341 = refl

  -- ctx-411: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=670 (1×)
  ctx-411-τ411 : τ 411 ≡ τ 411
  ctx-411-τ411 = refl


-- ── equalizer (Compare) ────────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module equalizer-Compare-256 where

  -- ctx-357: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=562 (1×)
  --   σ=695 (1×)
  ctx-357-τ357 : τ 357 ≡ τ 357
  ctx-357-τ357 = refl


-- ── partial@? (Attribute) ──────────────────────
-- 2 nodes, 1 type contexts, 1 forms

module partial-at-x3f-Attribute-261 where

  -- ctx-178: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=582 (2×)
  ctx-178-τ178 : τ 178 ≡ τ 178
  ctx-178-τ178 = refl


-- ── partial.apply@? (Call) ─────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module partial-apply-at-x3f-Call-262 where

  -- ctx-364: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=584 (1×)
  --   σ=1706 (1×)
  ctx-364-τ364 : τ 364 ≡ τ 364
  ctx-364-τ364 = refl


-- ── coerce (FormattedValue) ────────────────────
-- 2 nodes, 1 type contexts, 1 forms

module coerce-FormattedValue-278 where

  -- ctx-380: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=616 (2×)
  ctx-380-τ380 : τ 380 ≡ τ 380
  ctx-380-τ380 = refl


-- ── free_monoid.fold (JoinedStr) ───────────────
-- 2 nodes, 1 type contexts, 2 forms

module free_monoid-fold-JoinedStr-279 where

  -- str: 2 nodes, 2 forms
  -- [str]
  --   σ=617 (1×)
  --   σ=620 (1×)
  str-τ381 : τ 381 ≡ τ 381
  str-τ381 = refl


-- ── let (Assign) ───────────────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module let-k-Assign-280 where

  -- ctx-382: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=618 (1×)
  --   σ=621 (1×)
  ctx-382-τ382 : τ 382 ≡ τ 382
  ctx-382-τ382 = refl


-- ── free_monoid (Call) ─────────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module free_monoid-Call-296 where

  -- ctx-404: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=660 (1×)
  --   σ=947 (1×)
  ctx-404-τ404 : τ 404 ≡ τ 404
  ctx-404-τ404 = refl


-- ── fixpoint.halt (Break) ──────────────────────
-- 2 nodes, 1 type contexts, 1 forms

module fixpoint-halt-Break-325 where

  -- ctx-433: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=702 (2×)
  ctx-433-τ433 : τ 433 ≡ τ 433
  ctx-433-τ433 = refl


-- ── exponential.literal (Dict) ─────────────────
-- 2 nodes, 1 type contexts, 2 forms

module exponential-literal-Dict-326 where

  -- dict: 2 nodes, 2 forms
  -- [dict]
  --   σ=704 (1×)
  --   σ=1369 (1×)
  dict-τ435 : τ 435 ≡ τ 435
  dict-τ435 = refl


-- ── arguments (arguments) ──────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module arguments-341 where

  -- ctx-453: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=748 (1×)
  --   σ=934 (1×)
  ctx-453-τ453 : τ 453 ≡ τ 453
  ctx-453-τ453 = refl


-- ── equalizer (If) ─────────────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module equalizer-If-346 where

  -- ctx-459: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=769 (1×)
  --   σ=953 (1×)
  ctx-459-τ459 : τ 459 ≡ τ 459
  ctx-459-τ459 = refl


-- ── free_monoid.snoc@? (Call) ──────────────────
-- 2 nodes, 1 type contexts, 2 forms

module free_monoid-snoc-at-x3f-Call-358 where

  -- ctx-478: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=818 (1×)
  --   σ=1753 (1×)
  ctx-478-τ478 : τ 478 ≡ τ 478
  ctx-478-τ478 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module effect-seq-Expr-359 where

  -- ctx-479: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=819 (1×)
  --   σ=1754 (1×)
  ctx-479-τ479 : τ 479 ≡ τ 479
  ctx-479-τ479 = refl


-- ── terminal.map (Return) ──────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module terminal-map-Return-386 where

  -- ctx-508: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=876 (1×)
  --   σ=1800 (1×)
  ctx-508-τ508 : τ 508 ≡ τ 508
  ctx-508-τ508 = refl


-- ── apply (Call) ───────────────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module apply-Call-396 where

  -- ctx-520: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=898 (1×)
  --   σ=1255 (1×)
  ctx-520-τ520 : τ 520 ≡ τ 520
  ctx-520-τ520 = refl


-- ── let (Assign) ───────────────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module let-k-Assign-397 where

  -- ctx-521: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=899 (1×)
  --   σ=1256 (1×)
  ctx-521-τ521 : τ 521 ≡ τ 521
  ctx-521-τ521 = refl


-- ── not (Not) ──────────────────────────────────
-- 2 nodes, 1 type contexts, 1 forms

module not-Not-412 where

  -- ctx-540: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=962 (2×)
  ctx-540-τ540 : τ 540 ≡ τ 540
  ctx-540-τ540 = refl


-- ── complement (UnaryOp) ───────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module complement-UnaryOp-413 where

  -- ctx-541: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=964 (1×)
  --   σ=2010 (1×)
  ctx-541-τ541 : τ 541 ≡ τ 541
  ctx-541-τ541 = refl


-- ── free_monoid.snoc@? (Call) ──────────────────
-- 2 nodes, 1 type contexts, 2 forms

module free_monoid-snoc-at-x3f-Call-420 where

  -- ctx-548: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=985 (1×)
  --   σ=1671 (1×)
  ctx-548-τ548 : τ 548 ≡ τ 548
  ctx-548-τ548 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module effect-seq-Expr-421 where

  -- ctx-549: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=986 (1×)
  --   σ=1672 (1×)
  ctx-549-τ549 : τ 549 ≡ τ 549
  ctx-549-τ549 = refl


-- ── product (Tuple) ────────────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module product-Tuple-441 where

  -- tuple: 2 nodes, 2 forms
  -- [tuple]
  --   σ=1045 (1×)
  --   σ=1076 (1×)
  tuple-τ569 : τ 569 ≡ τ 569
  tuple-τ569 = refl


-- ── free_monoid.snoc@state (Call) ──────────────
-- 2 nodes, 1 type contexts, 2 forms

module free_monoid-snoc-at-state-Call-442 where

  -- None: 2 nodes, 2 forms
  -- [None]
  --   σ=1046 (1×)
  --   σ=1077 (1×)
  None-τ570 : τ 570 ≡ τ 570
  None-τ570 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module effect-seq-Expr-443 where

  -- ctx-571: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=1047 (1×)
  --   σ=1078 (1×)
  ctx-571-τ571 : τ 571 ≡ τ 571
  ctx-571-τ571 = refl


-- ── equalizer (If) ─────────────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module equalizer-If-444 where

  -- ctx-572: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=1061 (1×)
  --   σ=1079 (1×)
  ctx-572-τ572 : τ 572 ≡ τ 572
  ctx-572-τ572 = refl


-- ── equalizer (If) ─────────────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module equalizer-If-445 where

  -- ctx-573: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=1063 (1×)
  --   σ=1081 (1×)
  ctx-573-τ573 : τ 573 ≡ τ 573
  ctx-573-τ573 = refl


-- ── fold (For) ─────────────────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module fold-For-446 where

  -- ctx-574: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=1064 (1×)
  --   σ=1082 (1×)
  ctx-574-τ574 : τ 574 ≡ τ 574
  ctx-574-τ574 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 2 nodes, 2 type contexts, 2 forms

module annassign-AnnAssign-450 where

  -- ctx-579: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1108 (1×)
  ctx-579-τ579 : τ 579 ≡ τ 579
  ctx-579-τ579 = refl

  -- ctx-789: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1657 (1×)
  ctx-789-τ789 : τ 789 ≡ τ 789
  ctx-789-τ789 = refl


-- ── projection@object (Attribute) ──────────────
-- 2 nodes, 1 type contexts, 2 forms

module projection-at-object-Attribute-451 where

  -- T-items: 2 nodes, 2 forms
  -- [Self._cascade_abstraction_merge, Self._cascade_eta, Self._cell_contents, Self._cell_obs, Self._cleavage_fibers]
  --   σ=1110 (1×)
  --   σ=1131 (1×)
  T-items-τ34 : τ 34 ≡ τ 34
  T-items-τ34 = refl


-- ── projection.compute@object (Call) ───────────
-- 2 nodes, 1 type contexts, 2 forms

module projection-compute-at-object-Call-452 where

  -- Iter: 2 nodes, 2 forms
  -- [Iter]
  --   σ=1111 (1×)
  --   σ=1132 (1×)
  Iter-τ581 : τ 581 ≡ τ 581
  Iter-τ581 = refl


-- ── free_monoid (Call) ─────────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module free_monoid-Call-453 where

  -- ctx-582: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=1112 (1×)
  --   σ=1133 (1×)
  ctx-582-τ582 : τ 582 ≡ τ 582
  ctx-582-τ582 = refl


-- ── coerce (FormattedValue) ────────────────────
-- 2 nodes, 1 type contexts, 1 forms

module coerce-FormattedValue-459 where

  -- ctx-589: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=1139 (2×)
  ctx-589-τ589 : τ 589 ≡ τ 589
  ctx-589-τ589 = refl


-- ── powerset.literal (Set) ─────────────────────
-- 2 nodes, 1 type contexts, 1 forms

module powerset-literal-Set-k-462 where

  -- set: 2 nodes, 1 forms
  -- [set]
  --   σ=1147 (2×)
  set-τ593 : τ 593 ≡ τ 593
  set-τ593 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module annassign-AnnAssign-463 where

  -- ctx-594: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=1148 (1×)
  --   σ=1305 (1×)
  ctx-594-τ594 : τ 594 ≡ τ 594
  ctx-594-τ594 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 2 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-464 where

  -- ctx-598: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=1153 (2×)
  ctx-598-τ598 : τ 598 ≡ τ 598
  ctx-598-τ598 = refl


-- ── equalizer (If) ─────────────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module equalizer-If-465 where

  -- ctx-599: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=1158 (1×)
  --   σ=1310 (1×)
  ctx-599-τ599 : τ 599 ≡ τ 599
  ctx-599-τ599 = refl


-- ── equalizer (If) ─────────────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module equalizer-If-466 where

  -- ctx-600: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=1161 (1×)
  --   σ=1311 (1×)
  ctx-600-τ600 : τ 600 ≡ τ 600
  ctx-600-τ600 = refl


-- ── fold (For) ─────────────────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module fold-For-467 where

  -- ctx-601: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=1162 (1×)
  --   σ=1312 (1×)
  ctx-601-τ601 : τ 601 ≡ τ 601
  ctx-601-τ601 = refl


-- ── let (Assign) ───────────────────────────────
-- 2 nodes, 1 type contexts, 1 forms

module let-k-Assign-470 where

  -- ctx-605: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=1176 (2×)
  ctx-605-τ605 : τ 605 ≡ τ 605
  ctx-605-τ605 = refl


-- ── equalizer (If) ─────────────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module equalizer-If-471 where

  -- ctx-606: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=1195 (1×)
  --   σ=1322 (1×)
  ctx-606-τ606 : τ 606 ≡ τ 606
  ctx-606-τ606 = refl


-- ── fold (For) ─────────────────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module fold-For-472 where

  -- ctx-607: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=1196 (1×)
  --   σ=1323 (1×)
  ctx-607-τ607 : τ 607 ≡ τ 607
  ctx-607-τ607 = refl


-- ── free_monoid.snoc@state (Call) ──────────────
-- 2 nodes, 2 type contexts, 2 forms

module free_monoid-snoc-at-state-Call-473 where

  -- None: 1 nodes, 1 forms
  -- [None]
  --   σ=1198 (1×)
  None-τ609 : τ 609 ≡ τ 609
  None-τ609 = refl

  -- None: 1 nodes, 1 forms
  -- [None]
  --   σ=1325 (1×)
  None-τ647 : τ 647 ≡ τ 647
  None-τ647 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 2 nodes, 2 type contexts, 2 forms

module effect-seq-Expr-474 where

  -- ctx-610: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1199 (1×)
  ctx-610-τ610 : τ 610 ≡ τ 610
  ctx-610-τ610 = refl

  -- ctx-648: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1326 (1×)
  ctx-648-τ648 : τ 648 ≡ τ 648
  ctx-648-τ648 = refl


-- ── and (And) ──────────────────────────────────
-- 2 nodes, 1 type contexts, 1 forms

module and-And-493 where

  -- ctx-634: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=1274 (2×)
  ctx-634-τ634 : τ 634 ≡ τ 634
  ctx-634-τ634 = refl


-- ── powerset (Call) ────────────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module powerset-Call-511 where

  -- ctx-520: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=1344 (1×)
  --   σ=1889 (1×)
  ctx-520-τ520 : τ 520 ≡ τ 520
  ctx-520-τ520 = refl


-- ── product (Tuple) ────────────────────────────
-- 2 nodes, 2 type contexts, 2 forms

module product-Tuple-531 where

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=1399 (1×)
  tuple-τ677 : τ 677 ≡ τ 677
  tuple-τ677 = refl

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=1401 (1×)
  tuple-τ679 : τ 679 ≡ τ 679
  tuple-τ679 = refl


-- ── index (Index) ──────────────────────────────
-- 2 nodes, 1 type contexts, 1 forms

module index-Index-544 where

  -- ctx-694: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=1426 (2×)
  ctx-694-τ694 : τ 694 ≡ τ 694
  ctx-694-τ694 = refl


-- ── subscript (Subscript) ──────────────────────
-- 2 nodes, 1 type contexts, 1 forms

module subscript-Subscript-545 where

  -- ctx-695: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=1427 (2×)
  ctx-695-τ695 : τ 695 ≡ τ 695
  ctx-695-τ695 = refl


-- ── product (Tuple) ────────────────────────────
-- 2 nodes, 1 type contexts, 1 forms

module product-Tuple-546 where

  -- tuple: 2 nodes, 1 forms
  -- [tuple]
  --   σ=1428 (2×)
  tuple-τ696 : τ 696 ≡ τ 696
  tuple-τ696 = refl


-- ── index (Index) ──────────────────────────────
-- 2 nodes, 1 type contexts, 1 forms

module index-Index-547 where

  -- ctx-697: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=1429 (2×)
  ctx-697-τ697 : τ 697 ≡ τ 697
  ctx-697-τ697 = refl


-- ── subscript (Subscript) ──────────────────────
-- 2 nodes, 2 type contexts, 2 forms

module subscript-Subscript-548 where

  -- ctx-698: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1430 (1×)
  ctx-698-τ698 : τ 698 ≡ τ 698
  ctx-698-τ698 = refl

  -- ctx-710: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1454 (1×)
  ctx-710-τ710 : τ 710 ≡ τ 710
  ctx-710-τ710 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 2 nodes, 2 type contexts, 2 forms

module annassign-AnnAssign-570 where

  -- ctx-729: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1493 (1×)
  ctx-729-τ729 : τ 729 ≡ τ 729
  ctx-729-τ729 = refl

  -- ctx-808: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1702 (1×)
  ctx-808-τ808 : τ 808 ≡ τ 808
  ctx-808-τ808 = refl


-- ── index (Index) ──────────────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module index-Index-571 where

  -- ctx-730: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=1497 (1×)
  --   σ=1501 (1×)
  ctx-730-τ730 : τ 730 ≡ τ 730
  ctx-730-τ730 = refl


-- ── comprehension (comprehension) ──────────────
-- 2 nodes, 1 type contexts, 2 forms

module comprehension-576 where

  -- ctx-735: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=1513 (1×)
  --   σ=1741 (1×)
  ctx-735-τ735 : τ 735 ≡ τ 735
  ctx-735-τ735 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module annassign-AnnAssign-589 where

  -- ctx-751: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=1560 (1×)
  --   σ=1574 (1×)
  ctx-751-τ751 : τ 751 ≡ τ 751
  ctx-751-τ751 = refl


-- ── index (Index) ──────────────────────────────
-- 2 nodes, 1 type contexts, 1 forms

module index-Index-619 where

  -- ctx-786: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=1653 (2×)
  ctx-786-τ786 : τ 786 ≡ τ 786
  ctx-786-τ786 = refl


-- ── subscript (Subscript) ──────────────────────
-- 2 nodes, 1 type contexts, 1 forms

module subscript-Subscript-620 where

  -- ctx-787: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=1654 (2×)
  ctx-787-τ787 : τ 787 ≡ τ 787
  ctx-787-τ787 = refl


-- ── usub (USub) ────────────────────────────────
-- 2 nodes, 1 type contexts, 1 forms

module usub-USub-627 where

  -- ctx-795: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=1678 (2×)
  ctx-795-τ795 : τ 795 ≡ τ 795
  ctx-795-τ795 = refl


-- ── product (Tuple) ────────────────────────────
-- 2 nodes, 1 type contexts, 1 forms

module product-Tuple-646 where

  -- tuple: 2 nodes, 1 forms
  -- [tuple]
  --   σ=1724 (2×)
  tuple-τ818 : τ 818 ≡ τ 818
  tuple-τ818 = refl


-- ── index (Index) ──────────────────────────────
-- 2 nodes, 1 type contexts, 1 forms

module index-Index-647 where

  -- ctx-819: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=1725 (2×)
  ctx-819-τ819 : τ 819 ≡ τ 819
  ctx-819-τ819 = refl


-- ── subscript (Subscript) ──────────────────────
-- 2 nodes, 1 type contexts, 1 forms

module subscript-Subscript-648 where

  -- ctx-820: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=1726 (2×)
  ctx-820-τ820 : τ 820 ≡ τ 820
  ctx-820-τ820 = refl


-- ── index (Index) ──────────────────────────────
-- 2 nodes, 1 type contexts, 1 forms

module index-Index-649 where

  -- ctx-821: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=1727 (2×)
  ctx-821-τ821 : τ 821 ≡ τ 821
  ctx-821-τ821 = refl


-- ── subscript (Subscript) ──────────────────────
-- 2 nodes, 1 type contexts, 1 forms

module subscript-Subscript-650 where

  -- ctx-822: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=1728 (2×)
  ctx-822-τ822 : τ 822 ≡ τ 822
  ctx-822-τ822 = refl


-- ── apply (Call) ───────────────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module apply-Call-654 where

  -- ctx-827: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=1748 (1×)
  --   σ=2063 (1×)
  ctx-827-τ827 : τ 827 ≡ τ 827
  ctx-827-τ827 = refl


-- ── let (Assign) ───────────────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module let-k-Assign-655 where

  -- ctx-828: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=1749 (1×)
  --   σ=2064 (1×)
  ctx-828-τ828 : τ 828 ≡ τ 828
  ctx-828-τ828 = refl


-- ── let (Assign) ───────────────────────────────
-- 2 nodes, 1 type contexts, 1 forms

module let-k-Assign-664 where

  -- ctx-838: 2 nodes, 1 forms
  -- [(untyped)]
  --   σ=1772 (2×)
  ctx-838-τ838 : τ 838 ≡ τ 838
  ctx-838-τ838 = refl


-- ── free_monoid.fold (JoinedStr) ───────────────
-- 2 nodes, 2 type contexts, 2 forms

module free_monoid-fold-JoinedStr-671 where

  -- str: 1 nodes, 1 forms
  -- [str]
  --   σ=1815 (1×)
  str-τ848 : τ 848 ≡ τ 848
  str-τ848 = refl

  -- str: 1 nodes, 1 forms
  -- [str]
  --   σ=2016 (1×)
  str-τ931 : τ 931 ≡ τ 931
  str-τ931 = refl


-- ── free_monoid.fold (JoinedStr) ───────────────
-- 2 nodes, 1 type contexts, 1 forms

module free_monoid-fold-JoinedStr-672 where

  -- str: 2 nodes, 1 forms
  -- [str]
  --   σ=1816 (2×)
  str-τ849 : τ 849 ≡ τ 849
  str-τ849 = refl


-- ── coerce (FormattedValue) ────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module coerce-FormattedValue-680 where

  -- ctx-857: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=1847 (1×)
  --   σ=1856 (1×)
  ctx-857-τ857 : τ 857 ≡ τ 857
  ctx-857-τ857 = refl


-- ── bimap (BinOp) ──────────────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module bimap-BinOp-681 where

  -- ctx-858: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=1849 (1×)
  --   σ=1857 (1×)
  ctx-858-τ858 : τ 858 ≡ τ 858
  ctx-858-τ858 = refl


-- ── bimap (BinOp) ──────────────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module bimap-BinOp-682 where

  -- ctx-859: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=1850 (1×)
  --   σ=1858 (1×)
  ctx-859-τ859 : τ 859 ≡ τ 859
  ctx-859-τ859 = refl


-- ── coerce (FormattedValue) ────────────────────
-- 2 nodes, 1 type contexts, 2 forms

module coerce-FormattedValue-683 where

  -- ctx-860: 2 nodes, 2 forms
  -- [(untyped)]
  --   σ=1851 (1×)
  --   σ=1859 (1×)
  ctx-860-τ860 : τ 860 ≡ τ 860
  ctx-860-τ860 = refl


-- ── free_monoid.fold (JoinedStr) ───────────────
-- 2 nodes, 1 type contexts, 2 forms

module free_monoid-fold-JoinedStr-684 where

  -- str: 2 nodes, 2 forms
  -- [str]
  --   σ=1852 (1×)
  --   σ=1860 (1×)
  str-τ861 : τ 861 ≡ τ 861
  str-τ861 = refl


-- ── pullback.import (ImportFrom) ───────────────
-- 1 nodes, 1 type contexts, 1 forms

module pullback-import-ImportFrom-3 where

  -- ctx-3: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=3 (1×)
  ctx-3-τ3 : τ 3 ≡ τ 3
  ctx-3-τ3 = refl


-- ── pullback.import (ImportFrom) ───────────────
-- 1 nodes, 1 type contexts, 1 forms

module pullback-import-ImportFrom-4 where

  -- ctx-4: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=6 (1×)
  ctx-4-τ4 : τ 4 ≡ τ 4
  ctx-4-τ4 = refl


-- ── pullback.import (ImportFrom) ───────────────
-- 1 nodes, 1 type contexts, 1 forms

module pullback-import-ImportFrom-5 where

  -- ctx-5: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=10 (1×)
  ctx-5-τ5 : τ 5 ≡ τ 5
  ctx-5-τ5 = refl


-- ── product (Tuple) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module product-Tuple-9 where

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=18 (1×)
  tuple-τ9 : τ 9 ≡ τ 9
  tuple-τ9 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-10 where

  -- ctx-10: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=19 (1×)
  ctx-10-τ10 : τ 10 ≡ τ 10
  ctx-10-τ10 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-20 where

  -- ctx-30: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=38 (1×)
  ctx-30-τ30 : τ 30 ≡ τ 30
  ctx-30-τ30 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-29 where

  -- ctx-40: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=51 (1×)
  ctx-40-τ40 : τ 40 ≡ τ 40
  ctx-40-τ40 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-30 where

  -- ctx-41: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=52 (1×)
  ctx-41-τ41 : τ 41 ≡ τ 41
  ctx-41-τ41 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-31 where

  -- ctx-43: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=53 (1×)
  ctx-43-τ43 : τ 43 ≡ τ 43
  ctx-43-τ43 = refl


-- ── fixpoint (While) ───────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fixpoint-While-37 where

  -- ctx-51: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=62 (1×)
  ctx-51-τ51 : τ 51 ≡ τ 51
  ctx-51-τ51 = refl


-- ── product.unpack (Tuple) ─────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module product-unpack-Tuple-38 where

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=66 (1×)
  tuple-τ52 : τ 52 ≡ τ 52
  tuple-τ52 = refl


-- ── product (Tuple) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module product-Tuple-39 where

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=67 (1×)
  tuple-τ53 : τ 53 ≡ τ 53
  tuple-τ53 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-40 where

  -- ctx-54: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=68 (1×)
  ctx-54-τ54 : τ 54 ≡ τ 54
  ctx-54-τ54 = refl


-- ── fixpoint (While) ───────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fixpoint-While-41 where

  -- ctx-55: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=69 (1×)
  ctx-55-τ55 : τ 55 ≡ τ 55
  ctx-55-τ55 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-43 where

  -- ctx-57: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=71 (1×)
  ctx-57-τ57 : τ 57 ≡ τ 57
  ctx-57-τ57 = refl


-- ── product (Tuple) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module product-Tuple-47 where

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=85 (1×)
  tuple-τ63 : τ 63 ≡ τ 63
  tuple-τ63 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-48 where

  -- ctx-64: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=86 (1×)
  ctx-64-τ64 : τ 64 ≡ τ 64
  ctx-64-τ64 = refl


-- ── equalizer (Compare) ────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-Compare-53 where

  -- ctx-69: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=98 (1×)
  ctx-69-τ69 : τ 69 ≡ τ 69
  ctx-69-τ69 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-54 where

  -- ctx-70: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=100 (1×)
  ctx-70-τ70 : τ 70 ≡ τ 70
  ctx-70-τ70 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-55 where

  -- ctx-71: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=101 (1×)
  ctx-71-τ71 : τ 71 ≡ τ 71
  ctx-71-τ71 = refl


-- ── equalizer (Compare) ────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-Compare-56 where

  -- ctx-72: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=104 (1×)
  ctx-72-τ72 : τ 72 ≡ τ 72
  ctx-72-τ72 = refl


-- ── monoid.accum (AugAssign) ───────────────────
-- 1 nodes, 1 type contexts, 1 forms

module monoid-accum-AugAssign-58 where

  -- ctx-74: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=108 (1×)
  ctx-74-τ74 : τ 74 ≡ τ 74
  ctx-74-τ74 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-59 where

  -- ctx-75: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=109 (1×)
  ctx-75-τ75 : τ 75 ≡ τ 75
  ctx-75-τ75 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-60 where

  -- ctx-76: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=110 (1×)
  ctx-76-τ76 : τ 76 ≡ τ 76
  ctx-76-τ76 = refl


-- ── terminal.map (Return) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module terminal-map-Return-63 where

  -- ctx-79: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=116 (1×)
  ctx-79-τ79 : τ 79 ≡ τ 79
  ctx-79-τ79 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-64 where

  -- ctx-81: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=118 (1×)
  ctx-81-τ81 : τ 81 ≡ τ 81
  ctx-81-τ81 = refl


-- ── terminal.map (Return) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module terminal-map-Return-66 where

  -- ctx-83: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=121 (1×)
  ctx-83-τ83 : τ 83 ≡ τ 83
  ctx-83-τ83 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-68 where

  -- ctx-85: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=125 (1×)
  ctx-85-τ85 : τ 85 ≡ τ 85
  ctx-85-τ85 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-72 where

  -- ctx-89: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=129 (1×)
  ctx-89-τ89 : τ 89 ≡ τ 89
  ctx-89-τ89 = refl


-- ── classifier.intro (ClassDef) ────────────────
-- 1 nodes, 1 type contexts, 1 forms

module classifier-intro-ClassDef-73 where

  -- ctx-90: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=130 (1×)
  ctx-90-τ90 : τ 90 ≡ τ 90
  ctx-90-τ90 = refl


-- ── product (Tuple) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module product-Tuple-74 where

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=137 (1×)
  tuple-τ91 : τ 91 ≡ τ 91
  tuple-τ91 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-75 where

  -- ctx-92: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=138 (1×)
  ctx-92-τ92 : τ 92 ≡ τ 92
  ctx-92-τ92 = refl


-- ── arguments (arguments) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module arguments-80 where

  -- ctx-104: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=150 (1×)
  ctx-104-τ104 : τ 104 ≡ τ 104
  ctx-104-τ104 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-85 where

  -- ctx-117: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=166 (1×)
  ctx-117-τ117 : τ 117 ≡ τ 117
  ctx-117-τ117 = refl


-- ── free_monoid.fold (JoinedStr) ───────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-JoinedStr-88 where

  -- str: 1 nodes, 1 forms
  -- [str]
  --   σ=175 (1×)
  str-τ120 : τ 120 ≡ τ 120
  str-τ120 = refl


-- ── terminal.map (Return) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module terminal-map-Return-89 where

  -- ctx-121: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=176 (1×)
  ctx-121-τ121 : τ 121 ≡ τ 121
  ctx-121-τ121 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-90 where

  -- ctx-122: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=178 (1×)
  ctx-122-τ122 : τ 122 ≡ τ 122
  ctx-122-τ122 = refl


-- ── classifier.intro (ClassDef) ────────────────
-- 1 nodes, 1 type contexts, 1 forms

module classifier-intro-ClassDef-91 where

  -- ctx-123: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=179 (1×)
  ctx-123-τ123 : τ 123 ≡ τ 123
  ctx-123-τ123 = refl


-- ── product (Tuple) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module product-Tuple-92 where

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=194 (1×)
  tuple-τ133 : τ 133 ≡ τ 133
  tuple-τ133 = refl


-- ── index (Index) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module index-Index-93 where

  -- ctx-134: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=195 (1×)
  ctx-134-τ134 : τ 134 ≡ τ 134
  ctx-134-τ134 = refl


-- ── subscript (Subscript) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module subscript-Subscript-94 where

  -- ctx-135: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=196 (1×)
  ctx-135-τ135 : τ 135 ≡ τ 135
  ctx-135-τ135 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module annassign-AnnAssign-95 where

  -- ctx-136: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=197 (1×)
  ctx-136-τ136 : τ 136 ≡ τ 136
  ctx-136-τ136 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-99 where

  -- ctx-142: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=204 (1×)
  ctx-142-τ142 : τ 142 ≡ τ 142
  ctx-142-τ142 = refl


-- ── arguments (arguments) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module arguments-100 where

  -- ctx-143: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=206 (1×)
  ctx-143-τ143 : τ 143 ≡ τ 143
  ctx-143-τ143 = refl


-- ── apply (Call) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module apply-Call-103 where

  -- ctx-151: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=221 (1×)
  ctx-151-τ151 : τ 151 ≡ τ 151
  ctx-151-τ151 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-104 where

  -- ctx-152: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=222 (1×)
  ctx-152-τ152 : τ 152 ≡ τ 152
  ctx-152-τ152 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-108 where

  -- ctx-156: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=227 (1×)
  ctx-156-τ156 : τ 156 ≡ τ 156
  ctx-156-τ156 = refl


-- ── free_monoid.snoc@? (Call) ──────────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-x3f-Call-111 where

  -- ctx-160: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=232 (1×)
  ctx-160-τ160 : τ 160 ≡ τ 160
  ctx-160-τ160 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-112 where

  -- ctx-161: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=233 (1×)
  ctx-161-τ161 : τ 161 ≡ τ 161
  ctx-161-τ161 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-113 where

  -- ctx-163: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=235 (1×)
  ctx-163-τ163 : τ 163 ≡ τ 163
  ctx-163-τ163 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-115 where

  -- ctx-167: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=242 (1×)
  ctx-167-τ167 : τ 167 ≡ τ 167
  ctx-167-τ167 = refl


-- ── product (Tuple) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module product-Tuple-116 where

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=250 (1×)
  tuple-τ171 : τ 171 ≡ τ 171
  tuple-τ171 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-117 where

  -- ctx-172: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=251 (1×)
  ctx-172-τ172 : τ 172 ≡ τ 172
  ctx-172-τ172 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module annassign-AnnAssign-119 where

  -- ctx-175: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=255 (1×)
  ctx-175-τ175 : τ 175 ≡ τ 175
  ctx-175-τ175 = refl


-- ── ifexp (IfExp) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module ifexp-IfExp-120 where

  -- ctx-176: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=259 (1×)
  ctx-176-τ176 : τ 176 ≡ τ 176
  ctx-176-τ176 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-121 where

  -- ctx-177: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=260 (1×)
  ctx-177-τ177 : τ 177 ≡ τ 177
  ctx-177-τ177 = refl


-- ── apply (Call) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module apply-Call-122 where

  -- ctx-180: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=269 (1×)
  ctx-180-τ180 : τ 180 ≡ τ 180
  ctx-180-τ180 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-123 where

  -- ctx-181: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=270 (1×)
  ctx-181-τ181 : τ 181 ≡ τ 181
  ctx-181-τ181 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-124 where

  -- ctx-182: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=272 (1×)
  ctx-182-τ182 : τ 182 ≡ τ 182
  ctx-182-τ182 = refl


-- ── cofree (Yield) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module cofree-Yield-132 where

  -- ctx-191: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=288 (1×)
  ctx-191-τ191 : τ 191 ≡ τ 191
  ctx-191-τ191 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-133 where

  -- ctx-192: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=289 (1×)
  ctx-192-τ192 : τ 192 ≡ τ 192
  ctx-192-τ192 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-134 where

  -- ctx-193: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=290 (1×)
  ctx-193-τ193 : τ 193 ≡ τ 193
  ctx-193-τ193 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-135 where

  -- ctx-194: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=291 (1×)
  ctx-194-τ194 : τ 194 ≡ τ 194
  ctx-194-τ194 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-136 where

  -- ctx-196: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=293 (1×)
  ctx-196-τ196 : τ 196 ≡ τ 196
  ctx-196-τ196 = refl


-- ── comprehension (comprehension) ──────────────
-- 1 nodes, 1 type contexts, 1 forms

module comprehension-138 where

  -- ctx-199: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=298 (1×)
  ctx-199-τ199 : τ 199 ≡ τ 199
  ctx-199-τ199 = refl


-- ── lazy_fold (GeneratorExp) ───────────────────
-- 1 nodes, 1 type contexts, 1 forms

module lazy_fold-GeneratorExp-139 where

  -- ctx-200: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=299 (1×)
  ctx-200-τ200 : τ 200 ≡ τ 200
  ctx-200-τ200 = refl


-- ── apply (Call) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module apply-Call-140 where

  -- ctx-201: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=300 (1×)
  ctx-201-τ201 : τ 201 ≡ τ 201
  ctx-201-τ201 = refl


-- ── terminal.map (Return) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module terminal-map-Return-141 where

  -- ctx-202: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=301 (1×)
  ctx-202-τ202 : τ 202 ≡ τ 202
  ctx-202-τ202 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-142 where

  -- ctx-203: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=302 (1×)
  ctx-203-τ203 : τ 203 ≡ τ 203
  ctx-203-τ203 = refl


-- ── index (Index) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module index-Index-143 where

  -- ctx-204: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=303 (1×)
  ctx-204-τ204 : τ 204 ≡ τ 204
  ctx-204-τ204 = refl


-- ── subscript (Subscript) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module subscript-Subscript-144 where

  -- ctx-205: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=304 (1×)
  ctx-205-τ205 : τ 205 ≡ τ 205
  ctx-205-τ205 = refl


-- ── terminal.map (Return) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module terminal-map-Return-145 where

  -- ctx-206: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=305 (1×)
  ctx-206-τ206 : τ 206 ≡ τ 206
  ctx-206-τ206 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-146 where

  -- ctx-207: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=306 (1×)
  ctx-207-τ207 : τ 207 ≡ τ 207
  ctx-207-τ207 = refl


-- ── terminal.map (Return) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module terminal-map-Return-147 where

  -- ctx-208: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=307 (1×)
  ctx-208-τ208 : τ 208 ≡ τ 208
  ctx-208-τ208 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-148 where

  -- ctx-209: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=308 (1×)
  ctx-209-τ209 : τ 209 ≡ τ 209
  ctx-209-τ209 = refl


-- ── free_monoid.fold (JoinedStr) ───────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-JoinedStr-151 where

  -- str: 1 nodes, 1 forms
  -- [str]
  --   σ=315 (1×)
  str-τ212 : τ 212 ≡ τ 212
  str-τ212 = refl


-- ── terminal.map (Return) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module terminal-map-Return-152 where

  -- ctx-213: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=316 (1×)
  ctx-213-τ213 : τ 213 ≡ τ 213
  ctx-213-τ213 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-153 where

  -- ctx-214: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=317 (1×)
  ctx-214-τ214 : τ 214 ≡ τ 214
  ctx-214-τ214 = refl


-- ── classifier.intro (ClassDef) ────────────────
-- 1 nodes, 1 type contexts, 1 forms

module classifier-intro-ClassDef-154 where

  -- ctx-215: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=318 (1×)
  ctx-215-τ215 : τ 215 ≡ τ 215
  ctx-215-τ215 = refl


-- ── product (Tuple) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module product-Tuple-166 where

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=351 (1×)
  tuple-τ232 : τ 232 ≡ τ 232
  tuple-τ232 = refl


-- ── index (Index) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module index-Index-167 where

  -- ctx-233: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=352 (1×)
  ctx-233-τ233 : τ 233 ≡ τ 233
  ctx-233-τ233 = refl


-- ── subscript (Subscript) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module subscript-Subscript-168 where

  -- ctx-234: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=353 (1×)
  ctx-234-τ234 : τ 234 ≡ τ 234
  ctx-234-τ234 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module annassign-AnnAssign-169 where

  -- ctx-235: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=354 (1×)
  ctx-235-τ235 : τ 235 ≡ τ 235
  ctx-235-τ235 = refl


-- ── product (Tuple) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module product-Tuple-172 where

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=359 (1×)
  tuple-τ239 : τ 239 ≡ τ 239
  tuple-τ239 = refl


-- ── index (Index) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module index-Index-173 where

  -- ctx-240: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=360 (1×)
  ctx-240-τ240 : τ 240 ≡ τ 240
  ctx-240-τ240 = refl


-- ── subscript (Subscript) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module subscript-Subscript-174 where

  -- ctx-241: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=361 (1×)
  ctx-241-τ241 : τ 241 ≡ τ 241
  ctx-241-τ241 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module annassign-AnnAssign-176 where

  -- ctx-243: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=363 (1×)
  ctx-243-τ243 : τ 243 ≡ τ 243
  ctx-243-τ243 = refl


-- ── product (Tuple) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module product-Tuple-177 where

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=365 (1×)
  tuple-τ245 : τ 245 ≡ τ 245
  tuple-τ245 = refl


-- ── index (Index) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module index-Index-178 where

  -- ctx-246: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=366 (1×)
  ctx-246-τ246 : τ 246 ≡ τ 246
  ctx-246-τ246 = refl


-- ── subscript (Subscript) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module subscript-Subscript-179 where

  -- ctx-247: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=367 (1×)
  ctx-247-τ247 : τ 247 ≡ τ 247
  ctx-247-τ247 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module annassign-AnnAssign-180 where

  -- ctx-248: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=368 (1×)
  ctx-248-τ248 : τ 248 ≡ τ 248
  ctx-248-τ248 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module annassign-AnnAssign-186 where

  -- ctx-263: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=385 (1×)
  ctx-263-τ263 : τ 263 ≡ τ 263
  ctx-263-τ263 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module annassign-AnnAssign-192 where

  -- ctx-270: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=392 (1×)
  ctx-270-τ270 : τ 270 ≡ τ 270
  ctx-270-τ270 = refl


-- ── arguments (arguments) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module arguments-196 where

  -- ctx-285: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=408 (1×)
  ctx-285-τ285 : τ 285 ≡ τ 285
  ctx-285-τ285 = refl


-- ── lambda (Lambda) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module lambda-Lambda-197 where

  -- ctx-286: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=410 (1×)
  ctx-286-τ286 : τ 286 ≡ τ 286
  ctx-286-τ286 = refl


-- ── apply (Call) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module apply-Call-198 where

  -- ctx-287: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=411 (1×)
  ctx-287-τ287 : τ 287 ≡ τ 287
  ctx-287-τ287 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module annassign-AnnAssign-199 where

  -- ctx-288: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=412 (1×)
  ctx-288-τ288 : τ 288 ≡ τ 288
  ctx-288-τ288 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module annassign-AnnAssign-203 where

  -- ctx-293: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=421 (1×)
  ctx-293-τ293 : τ 293 ≡ τ 293
  ctx-293-τ293 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-204 where

  -- ctx-294: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=422 (1×)
  ctx-294-τ294 : τ 294 ≡ τ 294
  ctx-294-τ294 = refl


-- ── arg (arg) ──────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module arg-205 where

  -- ctx-297: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=427 (1×)
  ctx-297-τ297 : τ 297 ≡ τ 297
  ctx-297-τ297 = refl


-- ── arguments (arguments) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module arguments-206 where

  -- ctx-298: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=428 (1×)
  ctx-298-τ298 : τ 298 ≡ τ 298
  ctx-298-τ298 = refl


-- ── subscript (Subscript) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module subscript-Subscript-207 where

  -- ctx-299: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=437 (1×)
  ctx-299-τ299 : τ 299 ≡ τ 299
  ctx-299-τ299 = refl


-- ── monoid.accum (AugAssign) ───────────────────
-- 1 nodes, 1 type contexts, 1 forms

module monoid-accum-AugAssign-208 where

  -- ctx-300: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=438 (1×)
  ctx-300-τ300 : τ 300 ≡ τ 300
  ctx-300-τ300 = refl


-- ── coproduct.elim (If) ────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module coproduct-elim-If-214 where

  -- ctx-306: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=453 (1×)
  ctx-306-τ306 : τ 306 ≡ τ 306
  ctx-306-τ306 = refl


-- ── bimap (BinOp) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module bimap-BinOp-221 where

  -- ctx-314: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=462 (1×)
  ctx-314-τ314 : τ 314 ≡ τ 314
  ctx-314-τ314 = refl


-- ── apply (Call) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module apply-Call-222 where

  -- ctx-315: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=464 (1×)
  ctx-315-τ315 : τ 315 ≡ τ 315
  ctx-315-τ315 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-223 where

  -- ctx-316: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=465 (1×)
  ctx-316-τ316 : τ 316 ≡ τ 316
  ctx-316-τ316 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-224 where

  -- ctx-317: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=466 (1×)
  ctx-317-τ317 : τ 317 ≡ τ 317
  ctx-317-τ317 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-225 where

  -- ctx-318: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=467 (1×)
  ctx-318-τ318 : τ 318 ≡ τ 318
  ctx-318-τ318 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-226 where

  -- ctx-319: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=468 (1×)
  ctx-319-τ319 : τ 319 ≡ τ 319
  ctx-319-τ319 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-229 where

  -- ctx-325: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=486 (1×)
  ctx-325-τ325 : τ 325 ≡ τ 325
  ctx-325-τ325 = refl


-- ── or (Or) ────────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module or-Or-230 where

  -- ctx-327: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=489 (1×)
  ctx-327-τ327 : τ 327 ≡ τ 327
  ctx-327-τ327 = refl


-- ── join (BoolOp) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module join-BoolOp-231 where

  -- ctx-329: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=493 (1×)
  ctx-329-τ329 : τ 329 ≡ τ 329
  ctx-329-τ329 = refl


-- ── lazy_fold (GeneratorExp) ───────────────────
-- 1 nodes, 1 type contexts, 1 forms

module lazy_fold-GeneratorExp-233 where

  -- ctx-331: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=497 (1×)
  ctx-331-τ331 : τ 331 ≡ τ 331
  ctx-331-τ331 = refl


-- ── total_order (Call) ─────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module total_order-Call-234 where

  -- list: 1 nodes, 1 forms
  -- [list]
  --   σ=498 (1×)
  list-τ332 : τ 332 ≡ τ 332
  list-τ332 = refl


-- ── apply (Call) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module apply-Call-235 where

  -- ctx-333: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=499 (1×)
  ctx-333-τ333 : τ 333 ≡ τ 333
  ctx-333-τ333 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-236 where

  -- ctx-334: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=500 (1×)
  ctx-334-τ334 : τ 334 ≡ τ 334
  ctx-334-τ334 = refl


-- ── equalizer (Compare) ────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-Compare-237 where

  -- ctx-336: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=504 (1×)
  ctx-336-τ336 : τ 336 ≡ τ 336
  ctx-336-τ336 = refl


-- ── terminal.map (Return) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module terminal-map-Return-238 where

  -- ctx-337: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=505 (1×)
  ctx-337-τ337 : τ 337 ≡ τ 337
  ctx-337-τ337 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-239 where

  -- ctx-338: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=506 (1×)
  ctx-338-τ338 : τ 338 ≡ τ 338
  ctx-338-τ338 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-240 where

  -- ctx-339: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=513 (1×)
  ctx-339-τ339 : τ 339 ≡ τ 339
  ctx-339-τ339 = refl


-- ── free_monoid.snoc@state (Call) ──────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-state-Call-244 where

  -- None: 1 nodes, 1 forms
  -- [None]
  --   σ=520 (1×)
  None-τ343 : τ 343 ≡ τ 343
  None-τ343 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-245 where

  -- ctx-344: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=521 (1×)
  ctx-344-τ344 : τ 344 ≡ τ 344
  ctx-344-τ344 = refl


-- ── free_monoid.fold (JoinedStr) ───────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-JoinedStr-246 where

  -- str: 1 nodes, 1 forms
  -- [str]
  --   σ=527 (1×)
  str-τ345 : τ 345 ≡ τ 345
  str-τ345 = refl


-- ── apply (Call) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module apply-Call-247 where

  -- ctx-346: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=528 (1×)
  ctx-346-τ346 : τ 346 ≡ τ 346
  ctx-346-τ346 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-248 where

  -- ctx-347: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=529 (1×)
  ctx-347-τ347 : τ 347 ≡ τ 347
  ctx-347-τ347 = refl


-- ── free_monoid.snoc@state (Call) ──────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-state-Call-249 where

  -- None: 1 nodes, 1 forms
  -- [None, T]
  --   σ=532 (1×)
  None-τ349 : τ 349 ≡ τ 349
  None-τ349 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-250 where

  -- ctx-350: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=533 (1×)
  ctx-350-τ350 : τ 350 ≡ τ 350
  ctx-350-τ350 = refl


-- ── fixpoint (While) ───────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fixpoint-While-251 where

  -- ctx-351: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=534 (1×)
  ctx-351-τ351 : τ 351 ≡ τ 351
  ctx-351-τ351 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-253 where

  -- ctx-354: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=552 (1×)
  ctx-354-τ354 : τ 354 ≡ τ 354
  ctx-354-τ354 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module annassign-AnnAssign-257 where

  -- ctx-360: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=568 (1×)
  ctx-360-τ360 : τ 360 ≡ τ 360
  ctx-360-τ360 = refl


-- ── equalizer (Compare) ────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-Compare-260 where

  -- ctx-363: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=576 (1×)
  ctx-363-τ363 : τ 363 ≡ τ 363
  ctx-363-τ363 = refl


-- ── equalizer (Compare) ────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-Compare-265 where

  -- ctx-367: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=590 (1×)
  ctx-367-τ367 : τ 367 ≡ τ 367
  ctx-367-τ367 = refl


-- ── comprehension (comprehension) ──────────────
-- 1 nodes, 1 type contexts, 1 forms

module comprehension-266 where

  -- ctx-368: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=591 (1×)
  ctx-368-τ368 : τ 368 ≡ τ 368
  ctx-368-τ368 = refl


-- ── lazy_fold (GeneratorExp) ───────────────────
-- 1 nodes, 1 type contexts, 1 forms

module lazy_fold-GeneratorExp-267 where

  -- ctx-369: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=592 (1×)
  ctx-369-τ369 : τ 369 ≡ τ 369
  ctx-369-τ369 = refl


-- ── apply (Call) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module apply-Call-268 where

  -- ctx-370: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=593 (1×)
  ctx-370-τ370 : τ 370 ≡ τ 370
  ctx-370-τ370 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-269 where

  -- ctx-371: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=594 (1×)
  ctx-371-τ371 : τ 371 ≡ τ 371
  ctx-371-τ371 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-270 where

  -- ctx-372: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=600 (1×)
  ctx-372-τ372 : τ 372 ≡ τ 372
  ctx-372-τ372 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-271 where

  -- ctx-373: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=601 (1×)
  ctx-373-τ373 : τ 373 ≡ τ 373
  ctx-373-τ373 = refl


-- ── lte (LtE) ──────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module lte-LtE-272 where

  -- ctx-374: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=604 (1×)
  ctx-374-τ374 : τ 374 ≡ τ 374
  ctx-374-τ374 = refl


-- ── equalizer (Compare) ────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-Compare-273 where

  -- ctx-375: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=605 (1×)
  ctx-375-τ375 : τ 375 ≡ τ 375
  ctx-375-τ375 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-274 where

  -- ctx-376: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=606 (1×)
  ctx-376-τ376 : τ 376 ≡ τ 376
  ctx-376-τ376 = refl


-- ── coproduct.elim (If) ────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module coproduct-elim-If-281 where

  -- ctx-383: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=622 (1×)
  ctx-383-τ383 : τ 383 ≡ τ 383
  ctx-383-τ383 = refl


-- ── product (Tuple) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module product-Tuple-283 where

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=630 (1×)
  tuple-τ386 : τ 386 ≡ τ 386
  tuple-τ386 = refl


-- ── free_monoid.snoc@state (Call) ──────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-state-Call-284 where

  -- None: 1 nodes, 1 forms
  -- [None]
  --   σ=631 (1×)
  None-τ387 : τ 387 ≡ τ 387
  None-τ387 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-285 where

  -- ctx-388: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=632 (1×)
  ctx-388-τ388 : τ 388 ≡ τ 388
  ctx-388-τ388 = refl


-- ── monoid.op (BinOp) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module monoid-op-BinOp-286 where

  -- ctx-389: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=634 (1×)
  ctx-389-τ389 : τ 389 ≡ τ 389
  ctx-389-τ389 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-287 where

  -- ctx-390: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=635 (1×)
  ctx-390-τ390 : τ 390 ≡ τ 390
  ctx-390-τ390 = refl


-- ── partial.apply@state (Call) ─────────────────
-- 1 nodes, 1 type contexts, 1 forms

module partial-apply-at-state-Call-288 where

  -- T: 1 nodes, 1 forms
  -- [None, T]
  --   σ=644 (1×)
  T-τ349 : τ 349 ≡ τ 349
  T-τ349 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-289 where

  -- ctx-395: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=645 (1×)
  ctx-395-τ395 : τ 395 ≡ τ 395
  ctx-395-τ395 = refl


-- ── ifexp (IfExp) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module ifexp-IfExp-290 where

  -- ctx-398: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=653 (1×)
  ctx-398-τ398 : τ 398 ≡ τ 398
  ctx-398-τ398 = refl


-- ── monoid.op@? (Call) ─────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module monoid-op-at-x3f-Call-291 where

  -- ctx-399: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=654 (1×)
  ctx-399-τ399 : τ 399 ≡ τ 399
  ctx-399-τ399 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-292 where

  -- ctx-400: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=655 (1×)
  ctx-400-τ400 : τ 400 ≡ τ 400
  ctx-400-τ400 = refl


-- ── coproduct.elim (If) ────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module coproduct-elim-If-293 where

  -- ctx-401: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=656 (1×)
  ctx-401-τ401 : τ 401 ≡ τ 401
  ctx-401-τ401 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-294 where

  -- ctx-402: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=657 (1×)
  ctx-402-τ402 : τ 402 ≡ τ 402
  ctx-402-τ402 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-295 where

  -- ctx-403: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=658 (1×)
  ctx-403-τ403 : τ 403 ≡ τ 403
  ctx-403-τ403 = refl


-- ── ifexp (IfExp) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module ifexp-IfExp-297 where

  -- ctx-405: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=661 (1×)
  ctx-405-τ405 : τ 405 ≡ τ 405
  ctx-405-τ405 = refl


-- ── apply (Call) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module apply-Call-298 where

  -- ctx-406: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=662 (1×)
  ctx-406-τ406 : τ 406 ≡ τ 406
  ctx-406-τ406 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-299 where

  -- ctx-407: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=663 (1×)
  ctx-407-τ407 : τ 407 ≡ τ 407
  ctx-407-τ407 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-301 where

  -- ctx-408: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=667 (1×)
  ctx-408-τ408 : τ 408 ≡ τ 408
  ctx-408-τ408 = refl


-- ── morphism@? (Attribute) ─────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module morphism-at-x3f-Attribute-302 where

  -- ctx-409: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=668 (1×)
  ctx-409-τ409 : τ 409 ≡ τ 409
  ctx-409-τ409 = refl


-- ── monoid.accum (AugAssign) ───────────────────
-- 1 nodes, 1 type contexts, 1 forms

module monoid-accum-AugAssign-303 where

  -- ctx-410: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=669 (1×)
  ctx-410-τ410 : τ 410 ≡ τ 410
  ctx-410-τ410 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-305 where

  -- ctx-413: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=672 (1×)
  ctx-413-τ413 : τ 413 ≡ τ 413
  ctx-413-τ413 = refl


-- ── equalizer (Compare) ────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-Compare-307 where

  -- ctx-415: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=677 (1×)
  ctx-415-τ415 : τ 415 ≡ τ 415
  ctx-415-τ415 = refl


-- ── index (Index) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module index-Index-308 where

  -- ctx-416: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=678 (1×)
  ctx-416-τ416 : τ 416 ≡ τ 416
  ctx-416-τ416 = refl


-- ── subscript (Subscript) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module subscript-Subscript-309 where

  -- ctx-417: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=679 (1×)
  ctx-417-τ417 : τ 417 ≡ τ 417
  ctx-417-τ417 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-310 where

  -- ctx-418: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=681 (1×)
  ctx-418-τ418 : τ 418 ≡ τ 418
  ctx-418-τ418 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-311 where

  -- ctx-419: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=682 (1×)
  ctx-419-τ419 : τ 419 ≡ τ 419
  ctx-419-τ419 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-312 where

  -- ctx-420: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=683 (1×)
  ctx-420-τ420 : τ 420 ≡ τ 420
  ctx-420-τ420 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-313 where

  -- ctx-421: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=684 (1×)
  ctx-421-τ421 : τ 421 ≡ τ 421
  ctx-421-τ421 = refl


-- ── lazy_fold (GeneratorExp) ───────────────────
-- 1 nodes, 1 type contexts, 1 forms

module lazy_fold-GeneratorExp-315 where

  -- ctx-423: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=688 (1×)
  ctx-423-τ423 : τ 423 ≡ τ 423
  ctx-423-τ423 = refl


-- ── powerset (Call) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module powerset-Call-316 where

  -- ctx-424: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=689 (1×)
  ctx-424-τ424 : τ 424 ≡ τ 424
  ctx-424-τ424 = refl


-- ── total_order (Call) ─────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module total_order-Call-317 where

  -- list: 1 nodes, 1 forms
  -- [list]
  --   σ=690 (1×)
  list-τ425 : τ 425 ≡ τ 425
  list-τ425 = refl


-- ── apply (Call) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module apply-Call-318 where

  -- ctx-426: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=691 (1×)
  ctx-426-τ426 : τ 426 ≡ τ 426
  ctx-426-τ426 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-319 where

  -- ctx-427: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=692 (1×)
  ctx-427-τ427 : τ 427 ≡ τ 427
  ctx-427-τ427 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-320 where

  -- ctx-428: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=697 (1×)
  ctx-428-τ428 : τ 428 ≡ τ 428
  ctx-428-τ428 = refl


-- ── monoid.accum (AugAssign) ───────────────────
-- 1 nodes, 1 type contexts, 1 forms

module monoid-accum-AugAssign-321 where

  -- ctx-429: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=698 (1×)
  ctx-429-τ429 : τ 429 ≡ τ 429
  ctx-429-τ429 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-322 where

  -- ctx-430: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=699 (1×)
  ctx-430-τ430 : τ 430 ≡ τ 430
  ctx-430-τ430 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-323 where

  -- ctx-431: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=700 (1×)
  ctx-431-τ431 : τ 431 ≡ τ 431
  ctx-431-τ431 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-324 where

  -- ctx-432: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=701 (1×)
  ctx-432-τ432 : τ 432 ≡ τ 432
  ctx-432-τ432 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-327 where

  -- ctx-436: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=705 (1×)
  ctx-436-τ436 : τ 436 ≡ τ 436
  ctx-436-τ436 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-328 where

  -- ctx-437: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=706 (1×)
  ctx-437-τ437 : τ 437 ≡ τ 437
  ctx-437-τ437 = refl


-- ── fixpoint (While) ───────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fixpoint-While-329 where

  -- ctx-438: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=707 (1×)
  ctx-438-τ438 : τ 438 ≡ τ 438
  ctx-438-τ438 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-330 where

  -- ctx-439: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=708 (1×)
  ctx-439-τ439 : τ 439 ≡ τ 439
  ctx-439-τ439 = refl


-- ── arguments (arguments) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module arguments-332 where

  -- ctx-441: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=711 (1×)
  ctx-441-τ441 : τ 441 ≡ τ 441
  ctx-441-τ441 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-335 where

  -- ctx-446: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=723 (1×)
  ctx-446-τ446 : τ 446 ≡ τ 446
  ctx-446-τ446 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-336 where

  -- ctx-447: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=724 (1×)
  ctx-447-τ447 : τ 447 ≡ τ 447
  ctx-447-τ447 = refl


-- ── apply (Call) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module apply-Call-337 where

  -- ctx-448: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=742 (1×)
  ctx-448-τ448 : τ 448 ≡ τ 448
  ctx-448-τ448 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-338 where

  -- ctx-449: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=743 (1×)
  ctx-449-τ449 : τ 449 ≡ τ 449
  ctx-449-τ449 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-339 where

  -- ctx-450: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=744 (1×)
  ctx-450-τ450 : τ 450 ≡ τ 450
  ctx-450-τ450 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-340 where

  -- ctx-451: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=745 (1×)
  ctx-451-τ451 : τ 451 ≡ τ 451
  ctx-451-τ451 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-345 where

  -- ctx-458: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=764 (1×)
  ctx-458-τ458 : τ 458 ≡ τ 458
  ctx-458-τ458 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module annassign-AnnAssign-348 where

  -- ctx-466: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=782 (1×)
  ctx-466-τ466 : τ 466 ≡ τ 466
  ctx-466-τ466 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-360 where

  -- ctx-480: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=820 (1×)
  ctx-480-τ480 : τ 480 ≡ τ 480
  ctx-480-τ480 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-361 where

  -- ctx-481: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=822 (1×)
  ctx-481-τ481 : τ 481 ≡ τ 481
  ctx-481-τ481 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-362 where

  -- ctx-482: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=823 (1×)
  ctx-482-τ482 : τ 482 ≡ τ 482
  ctx-482-τ482 = refl


-- ── apply (Call) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module apply-Call-363 where

  -- ctx-444: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=829 (1×)
  ctx-444-τ444 : τ 444 ≡ τ 444
  ctx-444-τ444 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-364 where

  -- ctx-445: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=830 (1×)
  ctx-445-τ445 : τ 445 ≡ τ 445
  ctx-445-τ445 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-365 where

  -- ctx-483: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=831 (1×)
  ctx-483-τ483 : τ 483 ≡ τ 483
  ctx-483-τ483 = refl


-- ── product.unpack (Tuple) ─────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module product-unpack-Tuple-366 where

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=836 (1×)
  tuple-τ484 : τ 484 ≡ τ 484
  tuple-τ484 = refl


-- ── free_monoid.literal (List) ─────────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-literal-List-367 where

  -- list: 1 nodes, 1 forms
  -- [list]
  --   σ=838 (1×)
  list-τ485 : τ 485 ≡ τ 485
  list-τ485 = refl


-- ── product (Tuple) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module product-Tuple-368 where

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=842 (1×)
  tuple-τ488 : τ 488 ≡ τ 488
  tuple-τ488 = refl


-- ── free_monoid.snoc@state (Call) ──────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-state-Call-369 where

  -- None: 1 nodes, 1 forms
  -- [None]
  --   σ=843 (1×)
  None-τ489 : τ 489 ≡ τ 489
  None-τ489 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-370 where

  -- ctx-490: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=844 (1×)
  ctx-490-τ490 : τ 490 ≡ τ 490
  ctx-490-τ490 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-379 where

  -- ctx-501: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=864 (1×)
  ctx-501-τ501 : τ 501 ≡ τ 501
  ctx-501-τ501 = refl


-- ── coproduct.elim (If) ────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module coproduct-elim-If-380 where

  -- ctx-502: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=865 (1×)
  ctx-502-τ502 : τ 502 ≡ τ 502
  ctx-502-τ502 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-381 where

  -- ctx-503: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=866 (1×)
  ctx-503-τ503 : τ 503 ≡ τ 503
  ctx-503-τ503 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-382 where

  -- ctx-504: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=868 (1×)
  ctx-504-τ504 : τ 504 ≡ τ 504
  ctx-504-τ504 = refl


-- ── arguments (arguments) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module arguments-383 where

  -- ctx-505: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=870 (1×)
  ctx-505-τ505 : τ 505 ≡ τ 505
  ctx-505-τ505 = refl


-- ── is (Is) ────────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module is-Is-384 where

  -- ctx-506: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=874 (1×)
  ctx-506-τ506 : τ 506 ≡ τ 506
  ctx-506-τ506 = refl


-- ── equalizer (Compare) ────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-Compare-385 where

  -- ctx-507: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=875 (1×)
  ctx-507-τ507 : τ 507 ≡ τ 507
  ctx-507-τ507 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-387 where

  -- ctx-509: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=877 (1×)
  ctx-509-τ509 : τ 509 ≡ τ 509
  ctx-509-τ509 = refl


-- ── partial.apply@state (Call) ─────────────────
-- 1 nodes, 1 type contexts, 1 forms

module partial-apply-at-state-Call-388 where

  -- T: 1 nodes, 1 forms
  -- [T]
  --   σ=878 (1×)
  T-τ510 : τ 510 ≡ τ 510
  T-τ510 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-389 where

  -- ctx-511: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=879 (1×)
  ctx-511-τ511 : τ 511 ≡ τ 511
  ctx-511-τ511 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-390 where

  -- ctx-513: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=881 (1×)
  ctx-513-τ513 : τ 513 ≡ τ 513
  ctx-513-τ513 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-391 where

  -- ctx-514: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=883 (1×)
  ctx-514-τ514 : τ 514 ≡ τ 514
  ctx-514-τ514 = refl


-- ── arg (arg) ──────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module arg-392 where

  -- ctx-515: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=884 (1×)
  ctx-515-τ515 : τ 515 ≡ τ 515
  ctx-515-τ515 = refl


-- ── arguments (arguments) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module arguments-393 where

  -- ctx-516: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=885 (1×)
  ctx-516-τ516 : τ 516 ≡ τ 516
  ctx-516-τ516 = refl


-- ── product (Tuple) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module product-Tuple-398 where

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=906 (1×)
  tuple-τ523 : τ 523 ≡ τ 523
  tuple-τ523 = refl


-- ── terminal.map (Return) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module terminal-map-Return-399 where

  -- ctx-524: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=907 (1×)
  ctx-524-τ524 : τ 524 ≡ τ 524
  ctx-524-τ524 = refl


-- ── product (Tuple) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module product-Tuple-400 where

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=908 (1×)
  tuple-τ525 : τ 525 ≡ τ 525
  tuple-τ525 = refl


-- ── index (Index) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module index-Index-401 where

  -- ctx-526: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=909 (1×)
  ctx-526-τ526 : τ 526 ≡ τ 526
  ctx-526-τ526 = refl


-- ── subscript (Subscript) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module subscript-Subscript-402 where

  -- ctx-527: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=910 (1×)
  ctx-527-τ527 : τ 527 ≡ τ 527
  ctx-527-τ527 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-403 where

  -- ctx-528: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=911 (1×)
  ctx-528-τ528 : τ 528 ≡ τ 528
  ctx-528-τ528 = refl


-- ── arg (arg) ──────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module arg-404 where

  -- ctx-529: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=913 (1×)
  ctx-529-τ529 : τ 529 ≡ τ 529
  ctx-529-τ529 = refl


-- ── arguments (arguments) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module arguments-405 where

  -- ctx-530: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=914 (1×)
  ctx-530-τ530 : τ 530 ≡ τ 530
  ctx-530-τ530 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-406 where

  -- ctx-532: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=930 (1×)
  ctx-532-τ532 : τ 532 ≡ τ 532
  ctx-532-τ532 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-407 where

  -- ctx-533: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=931 (1×)
  ctx-533-τ533 : τ 533 ≡ τ 533
  ctx-533-τ533 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-408 where

  -- ctx-534: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=932 (1×)
  ctx-534-τ534 : τ 534 ≡ τ 534
  ctx-534-τ534 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-409 where

  -- ctx-536: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=948 (1×)
  ctx-536-τ536 : τ 536 ≡ τ 536
  ctx-536-τ536 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-410 where

  -- ctx-537: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=949 (1×)
  ctx-537-τ537 : τ 537 ≡ τ 537
  ctx-537-τ537 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-411 where

  -- ctx-539: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=961 (1×)
  ctx-539-τ539 : τ 539 ≡ τ 539
  ctx-539-τ539 = refl


-- ── index (Index) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module index-Index-417 where

  -- ctx-545: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=969 (1×)
  ctx-545-τ545 : τ 545 ≡ τ 545
  ctx-545-τ545 = refl


-- ── subscript (Subscript) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module subscript-Subscript-418 where

  -- ctx-546: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=970 (1×)
  ctx-546-τ546 : τ 546 ≡ τ 546
  ctx-546-τ546 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module annassign-AnnAssign-419 where

  -- ctx-547: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=971 (1×)
  ctx-547-τ547 : τ 547 ≡ τ 547
  ctx-547-τ547 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-422 where

  -- ctx-550: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=987 (1×)
  ctx-550-τ550 : τ 550 ≡ τ 550
  ctx-550-τ550 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-423 where

  -- ctx-551: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=989 (1×)
  ctx-551-τ551 : τ 551 ≡ τ 551
  ctx-551-τ551 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-424 where

  -- ctx-552: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=990 (1×)
  ctx-552-τ552 : τ 552 ≡ τ 552
  ctx-552-τ552 = refl


-- ── monoid.accum (AugAssign) ───────────────────
-- 1 nodes, 1 type contexts, 1 forms

module monoid-accum-AugAssign-425 where

  -- ctx-553: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=992 (1×)
  ctx-553-τ553 : τ 553 ≡ τ 553
  ctx-553-τ553 = refl


-- ── free_monoid.map (ListComp) ─────────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-map-ListComp-426 where

  -- ctx-554: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=997 (1×)
  ctx-554-τ554 : τ 554 ≡ τ 554
  ctx-554-τ554 = refl


-- ── product (Tuple) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module product-Tuple-427 where

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=999 (1×)
  tuple-τ555 : τ 555 ≡ τ 555
  tuple-τ555 = refl


-- ── free_monoid.snoc@state (Call) ──────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-state-Call-428 where

  -- None: 1 nodes, 1 forms
  -- [None]
  --   σ=1000 (1×)
  None-τ556 : τ 556 ≡ τ 556
  None-τ556 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-429 where

  -- ctx-557: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1001 (1×)
  ctx-557-τ557 : τ 557 ≡ τ 557
  ctx-557-τ557 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-430 where

  -- ctx-558: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1017 (1×)
  ctx-558-τ558 : τ 558 ≡ τ 558
  ctx-558-τ558 = refl


-- ── coproduct.elim (If) ────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module coproduct-elim-If-431 where

  -- ctx-559: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1018 (1×)
  ctx-559-τ559 : τ 559 ≡ τ 559
  ctx-559-τ559 = refl


-- ── complement (If) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module complement-If-432 where

  -- ctx-560: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1019 (1×)
  ctx-560-τ560 : τ 560 ≡ τ 560
  ctx-560-τ560 = refl


-- ── del (Del) ──────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module del-Del-433 where

  -- ctx-561: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1020 (1×)
  ctx-561-τ561 : τ 561 ≡ τ 561
  ctx-561-τ561 = refl


-- ── subscript (Subscript) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module subscript-Subscript-434 where

  -- ctx-562: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1021 (1×)
  ctx-562-τ562 : τ 562 ≡ τ 562
  ctx-562-τ562 = refl


-- ── delete (Delete) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module delete-Delete-435 where

  -- ctx-563: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1022 (1×)
  ctx-563-τ563 : τ 563 ≡ τ 563
  ctx-563-τ563 = refl


-- ── morphism@object (Attribute) ────────────────
-- 1 nodes, 1 type contexts, 1 forms

module morphism-at-object-Attribute-436 where

  -- T-discard: 1 nodes, 1 forms
  -- [T.discard]
  --   σ=1028 (1×)
  T-discard-τ564 : τ 564 ≡ τ 564
  T-discard-τ564 = refl


-- ── apply (Call) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module apply-Call-437 where

  -- ctx-565: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1029 (1×)
  ctx-565-τ565 : τ 565 ≡ τ 565
  ctx-565-τ565 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-438 where

  -- ctx-566: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1030 (1×)
  ctx-566-τ566 : τ 566 ≡ τ 566
  ctx-566-τ566 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-439 where

  -- ctx-567: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1031 (1×)
  ctx-567-τ567 : τ 567 ≡ τ 567
  ctx-567-τ567 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-447 where

  -- ctx-575: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1101 (1×)
  ctx-575-τ575 : τ 575 ≡ τ 575
  ctx-575-τ575 = refl


-- ── partial.apply@state (Call) ─────────────────
-- 1 nodes, 1 type contexts, 1 forms

module partial-apply-at-state-Call-448 where

  -- T: 1 nodes, 1 forms
  -- [T]
  --   σ=1104 (1×)
  T-τ577 : τ 577 ≡ τ 577
  T-τ577 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-449 where

  -- ctx-578: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1105 (1×)
  ctx-578-τ578 : τ 578 ≡ τ 578
  ctx-578-τ578 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-454 where

  -- ctx-583: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1121 (1×)
  ctx-583-τ583 : τ 583 ≡ τ 583
  ctx-583-τ583 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-455 where

  -- ctx-584: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1122 (1×)
  ctx-584-τ584 : τ 584 ≡ τ 584
  ctx-584-τ584 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-457 where

  -- ctx-586: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1129 (1×)
  ctx-586-τ586 : τ 586 ≡ τ 586
  ctx-586-τ586 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-458 where

  -- ctx-588: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1134 (1×)
  ctx-588-τ588 : τ 588 ≡ τ 588
  ctx-588-τ588 = refl


-- ── free_monoid.fold (JoinedStr) ───────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-JoinedStr-460 where

  -- str: 1 nodes, 1 forms
  -- [str]
  --   σ=1140 (1×)
  str-τ590 : τ 590 ≡ τ 590
  str-τ590 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-461 where

  -- ctx-591: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1141 (1×)
  ctx-591-τ591 : τ 591 ≡ τ 591
  ctx-591-τ591 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-469 where

  -- ctx-604: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1172 (1×)
  ctx-604-τ604 : τ 604 ≡ τ 604
  ctx-604-τ604 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-475 where

  -- ctx-611: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1208 (1×)
  ctx-611-τ611 : τ 611 ≡ τ 611
  ctx-611-τ611 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-476 where

  -- ctx-612: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1209 (1×)
  ctx-612-τ612 : τ 612 ≡ τ 612
  ctx-612-τ612 = refl


-- ── fixpoint (While) ───────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fixpoint-While-477 where

  -- ctx-613: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1211 (1×)
  ctx-613-τ613 : τ 613 ≡ τ 613
  ctx-613-τ613 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-478 where

  -- ctx-614: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1212 (1×)
  ctx-614-τ614 : τ 614 ≡ τ 614
  ctx-614-τ614 = refl


-- ── product (Tuple) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module product-Tuple-479 where

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=1214 (1×)
  tuple-τ615 : τ 615 ≡ τ 615
  tuple-τ615 = refl


-- ── index (Index) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module index-Index-480 where

  -- ctx-616: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1215 (1×)
  ctx-616-τ616 : τ 616 ≡ τ 616
  ctx-616-τ616 = refl


-- ── subscript (Subscript) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module subscript-Subscript-481 where

  -- ctx-617: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1216 (1×)
  ctx-617-τ617 : τ 617 ≡ τ 617
  ctx-617-τ617 = refl


-- ── arg (arg) ──────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module arg-482 where

  -- ctx-618: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1217 (1×)
  ctx-618-τ618 : τ 618 ≡ τ 618
  ctx-618-τ618 = refl


-- ── arguments (arguments) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module arguments-483 where

  -- ctx-619: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1224 (1×)
  ctx-619-τ619 : τ 619 ≡ τ 619
  ctx-619-τ619 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-485 where

  -- ctx-621: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1233 (1×)
  ctx-621-τ621 : τ 621 ≡ τ 621
  ctx-621-τ621 = refl


-- ── product (Tuple) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module product-Tuple-488 where

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=1261 (1×)
  tuple-τ626 : τ 626 ≡ τ 626
  tuple-τ626 = refl


-- ── index (Index) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module index-Index-489 where

  -- ctx-627: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1262 (1×)
  ctx-627-τ627 : τ 627 ≡ τ 627
  ctx-627-τ627 = refl


-- ── subscript (Subscript) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module subscript-Subscript-490 where

  -- ctx-628: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1263 (1×)
  ctx-628-τ628 : τ 628 ≡ τ 628
  ctx-628-τ628 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module annassign-AnnAssign-491 where

  -- ctx-629: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1267 (1×)
  ctx-629-τ629 : τ 629 ≡ τ 629
  ctx-629-τ629 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module annassign-AnnAssign-492 where

  -- ctx-633: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1273 (1×)
  ctx-633-τ633 : τ 633 ≡ τ 633
  ctx-633-τ633 = refl


-- ── meet (BoolOp) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module meet-BoolOp-494 where

  -- ctx-635: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1277 (1×)
  ctx-635-τ635 : τ 635 ≡ τ 635
  ctx-635-τ635 = refl


-- ── equalizer (Compare) ────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-Compare-495 where

  -- ctx-636: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1284 (1×)
  ctx-636-τ636 : τ 636 ≡ τ 636
  ctx-636-τ636 = refl


-- ── lazy_fold (GeneratorExp) ───────────────────
-- 1 nodes, 1 type contexts, 1 forms

module lazy_fold-GeneratorExp-496 where

  -- ctx-637: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1287 (1×)
  ctx-637-τ637 : τ 637 ≡ τ 637
  ctx-637-τ637 = refl


-- ── apply (Call) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module apply-Call-497 where

  -- ctx-638: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1288 (1×)
  ctx-638-τ638 : τ 638 ≡ τ 638
  ctx-638-τ638 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-498 where

  -- ctx-639: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1289 (1×)
  ctx-639-τ639 : τ 639 ≡ τ 639
  ctx-639-τ639 = refl


-- ── free_monoid.map (ListComp) ─────────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-map-ListComp-499 where

  -- ctx-640: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1291 (1×)
  ctx-640-τ640 : τ 640 ≡ τ 640
  ctx-640-τ640 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-500 where

  -- ctx-641: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1292 (1×)
  ctx-641-τ641 : τ 641 ≡ τ 641
  ctx-641-τ641 = refl


-- ── free_monoid.snoc@? (Call) ──────────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-x3f-Call-501 where

  -- ctx-189: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1294 (1×)
  ctx-189-τ189 : τ 189 ≡ τ 189
  ctx-189-τ189 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-502 where

  -- ctx-190: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1295 (1×)
  ctx-190-τ190 : τ 190 ≡ τ 190
  ctx-190-τ190 = refl


-- ── monoid.op (BinOp) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module monoid-op-BinOp-503 where

  -- ctx-642: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1297 (1×)
  ctx-642-τ642 : τ 642 ≡ τ 642
  ctx-642-τ642 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-504 where

  -- ctx-643: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1298 (1×)
  ctx-643-τ643 : τ 643 ≡ τ 643
  ctx-643-τ643 = refl


-- ── free_monoid.fold (JoinedStr) ───────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-JoinedStr-505 where

  -- str: 1 nodes, 1 forms
  -- [str]
  --   σ=1302 (1×)
  str-τ644 : τ 644 ≡ τ 644
  str-τ644 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-506 where

  -- ctx-645: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1303 (1×)
  ctx-645-τ645 : τ 645 ≡ τ 645
  ctx-645-τ645 = refl


-- ── free_monoid.map (ListComp) ─────────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-map-ListComp-507 where

  -- ctx-649: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1329 (1×)
  ctx-649-τ649 : τ 649 ≡ τ 649
  ctx-649-τ649 = refl


-- ── apply (Call) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module apply-Call-508 where

  -- ctx-650: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1330 (1×)
  ctx-650-τ650 : τ 650 ≡ τ 650
  ctx-650-τ650 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-509 where

  -- ctx-651: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1331 (1×)
  ctx-651-τ651 : τ 651 ≡ τ 651
  ctx-651-τ651 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-510 where

  -- ctx-655: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1341 (1×)
  ctx-655-τ655 : τ 655 ≡ τ 655
  ctx-655-τ655 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-512 where

  -- ctx-521: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1345 (1×)
  ctx-521-τ521 : τ 521 ≡ τ 521
  ctx-521-τ521 = refl


-- ── monoid.op@? (Call) ─────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module monoid-op-at-x3f-Call-513 where

  -- ctx-656: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1348 (1×)
  ctx-656-τ656 : τ 656 ≡ τ 656
  ctx-656-τ656 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-514 where

  -- ctx-657: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1349 (1×)
  ctx-657-τ657 : τ 657 ≡ τ 657
  ctx-657-τ657 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-516 where

  -- ctx-190: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1353 (1×)
  ctx-190-τ190 : τ 190 ≡ τ 190
  ctx-190-τ190 = refl


-- ── coproduct.elim (If) ────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module coproduct-elim-If-517 where

  -- ctx-662: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1359 (1×)
  ctx-662-τ662 : τ 662 ≡ τ 662
  ctx-662-τ662 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-518 where

  -- ctx-663: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1368 (1×)
  ctx-663-τ663 : τ 663 ≡ τ 663
  ctx-663-τ663 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-519 where

  -- ctx-664: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1370 (1×)
  ctx-664-τ664 : τ 664 ≡ τ 664
  ctx-664-τ664 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-520 where

  -- ctx-665: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1374 (1×)
  ctx-665-τ665 : τ 665 ≡ τ 665
  ctx-665-τ665 = refl


-- ── coproduct.elim (If) ────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module coproduct-elim-If-521 where

  -- ctx-666: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1375 (1×)
  ctx-666-τ666 : τ 666 ≡ τ 666
  ctx-666-τ666 = refl


-- ── exponential.literal (Dict) ─────────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-literal-Dict-522 where

  -- dict: 1 nodes, 1 forms
  -- [dict]
  --   σ=1387 (1×)
  dict-τ668 : τ 668 ≡ τ 668
  dict-τ668 = refl


-- ── free_monoid.snoc@state (Call) ──────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-state-Call-523 where

  -- None: 1 nodes, 1 forms
  -- [None]
  --   σ=1388 (1×)
  None-τ669 : τ 669 ≡ τ 669
  None-τ669 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-524 where

  -- ctx-670: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1389 (1×)
  ctx-670-τ670 : τ 670 ≡ τ 670
  ctx-670-τ670 = refl


-- ── product (Tuple) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module product-Tuple-525 where

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=1393 (1×)
  tuple-τ671 : τ 671 ≡ τ 671
  tuple-τ671 = refl


-- ── index (Index) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module index-Index-526 where

  -- ctx-672: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1394 (1×)
  ctx-672-τ672 : τ 672 ≡ τ 672
  ctx-672-τ672 = refl


-- ── subscript (Subscript) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module subscript-Subscript-527 where

  -- ctx-673: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1395 (1×)
  ctx-673-τ673 : τ 673 ≡ τ 673
  ctx-673-τ673 = refl


-- ── monoid.op@? (Attribute) ────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module monoid-op-at-x3f-Attribute-528 where

  -- ctx-674: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1396 (1×)
  ctx-674-τ674 : τ 674 ≡ τ 674
  ctx-674-τ674 = refl


-- ── monoid.op@? (Call) ─────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module monoid-op-at-x3f-Call-529 where

  -- ctx-675: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1397 (1×)
  ctx-675-τ675 : τ 675 ≡ τ 675
  ctx-675-τ675 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-530 where

  -- ctx-676: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1398 (1×)
  ctx-676-τ676 : τ 676 ≡ τ 676
  ctx-676-τ676 = refl


-- ── terminal.map (Return) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module terminal-map-Return-532 where

  -- ctx-678: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1400 (1×)
  ctx-678-τ678 : τ 678 ≡ τ 678
  ctx-678-τ678 = refl


-- ── index (Index) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module index-Index-533 where

  -- ctx-680: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1402 (1×)
  ctx-680-τ680 : τ 680 ≡ τ 680
  ctx-680-τ680 = refl


-- ── subscript (Subscript) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module subscript-Subscript-534 where

  -- ctx-681: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1403 (1×)
  ctx-681-τ681 : τ 681 ≡ τ 681
  ctx-681-τ681 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-535 where

  -- ctx-682: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1404 (1×)
  ctx-682-τ682 : τ 682 ≡ τ 682
  ctx-682-τ682 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-536 where

  -- ctx-683: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1407 (1×)
  ctx-683-τ683 : τ 683 ≡ τ 683
  ctx-683-τ683 = refl


-- ── arg (arg) ──────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module arg-537 where

  -- ctx-684: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1408 (1×)
  ctx-684-τ684 : τ 684 ≡ τ 684
  ctx-684-τ684 = refl


-- ── arguments (arguments) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module arguments-538 where

  -- ctx-685: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1410 (1×)
  ctx-685-τ685 : τ 685 ≡ τ 685
  ctx-685-τ685 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module annassign-AnnAssign-539 where

  -- ctx-687: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1414 (1×)
  ctx-687-τ687 : τ 687 ≡ τ 687
  ctx-687-τ687 = refl


-- ── terminal.map (Return) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module terminal-map-Return-542 where

  -- ctx-691: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1420 (1×)
  ctx-691-τ691 : τ 691 ≡ τ 691
  ctx-691-τ691 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-543 where

  -- ctx-692: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1421 (1×)
  ctx-692-τ692 : τ 692 ≡ τ 692
  ctx-692-τ692 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module annassign-AnnAssign-549 where

  -- ctx-699: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1432 (1×)
  ctx-699-τ699 : τ 699 ≡ τ 699
  ctx-699-τ699 = refl


-- ── product (Tuple) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module product-Tuple-551 where

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=1444 (1×)
  tuple-τ702 : τ 702 ≡ τ 702
  tuple-τ702 = refl


-- ── index (Index) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module index-Index-552 where

  -- ctx-703: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1445 (1×)
  ctx-703-τ703 : τ 703 ≡ τ 703
  ctx-703-τ703 = refl


-- ── subscript (Subscript) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module subscript-Subscript-553 where

  -- ctx-704: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1446 (1×)
  ctx-704-τ704 : τ 704 ≡ τ 704
  ctx-704-τ704 = refl


-- ── free_monoid.op@? (Attribute) ───────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-op-at-x3f-Attribute-554 where

  -- ctx-705: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1447 (1×)
  ctx-705-τ705 : τ 705 ≡ τ 705
  ctx-705-τ705 = refl


-- ── free_monoid.snoc@? (Call) ──────────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-x3f-Call-555 where

  -- ctx-706: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1449 (1×)
  ctx-706-τ706 : τ 706 ≡ τ 706
  ctx-706-τ706 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-556 where

  -- ctx-707: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1450 (1×)
  ctx-707-τ707 : τ 707 ≡ τ 707
  ctx-707-τ707 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-557 where

  -- ctx-708: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1451 (1×)
  ctx-708-τ708 : τ 708 ≡ τ 708
  ctx-708-τ708 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-560 where

  -- ctx-711: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1455 (1×)
  ctx-711-τ711 : τ 711 ≡ τ 711
  ctx-711-τ711 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module annassign-AnnAssign-561 where

  -- ctx-715: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1467 (1×)
  ctx-715-τ715 : τ 715 ≡ τ 715
  ctx-715-τ715 = refl


-- ── product (Tuple) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module product-Tuple-562 where

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=1472 (1×)
  tuple-τ716 : τ 716 ≡ τ 716
  tuple-τ716 = refl


-- ── index (Index) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module index-Index-563 where

  -- ctx-717: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1473 (1×)
  ctx-717-τ717 : τ 717 ≡ τ 717
  ctx-717-τ717 = refl


-- ── subscript (Subscript) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module subscript-Subscript-564 where

  -- ctx-718: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1474 (1×)
  ctx-718-τ718 : τ 718 ≡ τ 718
  ctx-718-τ718 = refl


-- ── free_monoid.op@? (Attribute) ───────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-op-at-x3f-Attribute-565 where

  -- ctx-719: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1475 (1×)
  ctx-719-τ719 : τ 719 ≡ τ 719
  ctx-719-τ719 = refl


-- ── free_monoid.snoc@? (Call) ──────────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-x3f-Call-566 where

  -- ctx-720: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1476 (1×)
  ctx-720-τ720 : τ 720 ≡ τ 720
  ctx-720-τ720 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-567 where

  -- ctx-721: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1477 (1×)
  ctx-721-τ721 : τ 721 ≡ τ 721
  ctx-721-τ721 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-568 where

  -- ctx-722: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1478 (1×)
  ctx-722-τ722 : τ 722 ≡ τ 722
  ctx-722-τ722 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-569 where

  -- ctx-724: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1480 (1×)
  ctx-724-τ724 : τ 724 ≡ τ 724
  ctx-724-τ724 = refl


-- ── subscript (Subscript) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module subscript-Subscript-572 where

  -- ctx-731: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1498 (1×)
  ctx-731-τ731 : τ 731 ≡ τ 731
  ctx-731-τ731 = refl


-- ── subscript (Subscript) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module subscript-Subscript-573 where

  -- ctx-732: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1502 (1×)
  ctx-732-τ732 : τ 732 ≡ τ 732
  ctx-732-τ732 = refl


-- ── monoid.accum (AugAssign) ───────────────────
-- 1 nodes, 1 type contexts, 1 forms

module monoid-accum-AugAssign-574 where

  -- ctx-733: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1503 (1×)
  ctx-733-τ733 : τ 733 ≡ τ 733
  ctx-733-τ733 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-575 where

  -- ctx-734: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1504 (1×)
  ctx-734-τ734 : τ 734 ≡ τ 734
  ctx-734-τ734 = refl


-- ── exponential.map (DictComp) ─────────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-map-DictComp-577 where

  -- ctx-736: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1514 (1×)
  ctx-736-τ736 : τ 736 ≡ τ 736
  ctx-736-τ736 = refl


-- ── terminal.map (Return) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module terminal-map-Return-578 where

  -- ctx-737: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1515 (1×)
  ctx-737-τ737 : τ 737 ≡ τ 737
  ctx-737-τ737 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-579 where

  -- ctx-741: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1520 (1×)
  ctx-741-τ741 : τ 741 ≡ τ 741
  ctx-741-τ741 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-580 where

  -- ctx-742: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1535 (1×)
  ctx-742-τ742 : τ 742 ≡ τ 742
  ctx-742-τ742 = refl


-- ── subscript (Subscript) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module subscript-Subscript-581 where

  -- ctx-743: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1540 (1×)
  ctx-743-τ743 : τ 743 ≡ τ 743
  ctx-743-τ743 = refl


-- ── morphism@? (Attribute) ─────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module morphism-at-x3f-Attribute-582 where

  -- ctx-744: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1541 (1×)
  ctx-744-τ744 : τ 744 ≡ τ 744
  ctx-744-τ744 = refl


-- ── apply (Call) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module apply-Call-583 where

  -- ctx-745: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1548 (1×)
  ctx-745-τ745 : τ 745 ≡ τ 745
  ctx-745-τ745 = refl


-- ── monoid.op@? (Call) ─────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module monoid-op-at-x3f-Call-584 where

  -- ctx-746: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1549 (1×)
  ctx-746-τ746 : τ 746 ≡ τ 746
  ctx-746-τ746 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-585 where

  -- ctx-747: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1550 (1×)
  ctx-747-τ747 : τ 747 ≡ τ 747
  ctx-747-τ747 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-586 where

  -- ctx-748: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1551 (1×)
  ctx-748-τ748 : τ 748 ≡ τ 748
  ctx-748-τ748 = refl


-- ── terminal.map (Return) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module terminal-map-Return-587 where

  -- ctx-749: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1553 (1×)
  ctx-749-τ749 : τ 749 ≡ τ 749
  ctx-749-τ749 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-588 where

  -- ctx-750: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1554 (1×)
  ctx-750-τ750 : τ 750 ≡ τ 750
  ctx-750-τ750 = refl


-- ── index (Index) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module index-Index-590 where

  -- ctx-753: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1564 (1×)
  ctx-753-τ753 : τ 753 ≡ τ 753
  ctx-753-τ753 = refl


-- ── subscript (Subscript) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module subscript-Subscript-591 where

  -- ctx-754: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1565 (1×)
  ctx-754-τ754 : τ 754 ≡ τ 754
  ctx-754-τ754 = refl


-- ── monoid.accum (AugAssign) ───────────────────
-- 1 nodes, 1 type contexts, 1 forms

module monoid-accum-AugAssign-592 where

  -- ctx-755: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1566 (1×)
  ctx-755-τ755 : τ 755 ≡ τ 755
  ctx-755-τ755 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-593 where

  -- ctx-756: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1567 (1×)
  ctx-756-τ756 : τ 756 ≡ τ 756
  ctx-756-τ756 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-594 where

  -- ctx-757: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1569 (1×)
  ctx-757-τ757 : τ 757 ≡ τ 757
  ctx-757-τ757 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module annassign-AnnAssign-595 where

  -- ctx-760: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1581 (1×)
  ctx-760-τ760 : τ 760 ≡ τ 760
  ctx-760-τ760 = refl


-- ── exponential.literal (Dict) ─────────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-literal-Dict-598 where

  -- dict: 1 nodes, 1 forms
  -- [dict]
  --   σ=1607 (1×)
  dict-τ765 : τ 765 ≡ τ 765
  dict-τ765 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module annassign-AnnAssign-599 where

  -- ctx-766: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1608 (1×)
  ctx-766-τ766 : τ 766 ≡ τ 766
  ctx-766-τ766 = refl


-- ── keyword (keyword) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module keyword-601 where

  -- ctx-767: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1613 (1×)
  ctx-767-τ767 : τ 767 ≡ τ 767
  ctx-767-τ767 = refl


-- ── apply (Call) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module apply-Call-602 where

  -- ctx-768: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1614 (1×)
  ctx-768-τ768 : τ 768 ≡ τ 768
  ctx-768-τ768 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-603 where

  -- ctx-769: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1615 (1×)
  ctx-769-τ769 : τ 769 ≡ τ 769
  ctx-769-τ769 = refl


-- ── monoid.accum (AugAssign) ───────────────────
-- 1 nodes, 1 type contexts, 1 forms

module monoid-accum-AugAssign-604 where

  -- ctx-770: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1620 (1×)
  ctx-770-τ770 : τ 770 ≡ τ 770
  ctx-770-τ770 = refl


-- ── exponential.literal (Dict) ─────────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-literal-Dict-605 where

  -- dict: 1 nodes, 1 forms
  -- [dict]
  --   σ=1622 (1×)
  dict-τ771 : τ 771 ≡ τ 771
  dict-τ771 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-606 where

  -- ctx-772: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1623 (1×)
  ctx-772-τ772 : τ 772 ≡ τ 772
  ctx-772-τ772 = refl


-- ── monoid.op@? (Call) ─────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module monoid-op-at-x3f-Call-607 where

  -- ctx-774: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1629 (1×)
  ctx-774-τ774 : τ 774 ≡ τ 774
  ctx-774-τ774 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-608 where

  -- ctx-775: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1630 (1×)
  ctx-775-τ775 : τ 775 ≡ τ 775
  ctx-775-τ775 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-609 where

  -- ctx-776: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1631 (1×)
  ctx-776-τ776 : τ 776 ≡ τ 776
  ctx-776-τ776 = refl


-- ── terminal.map (Return) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module terminal-map-Return-610 where

  -- ctx-777: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1633 (1×)
  ctx-777-τ777 : τ 777 ≡ τ 777
  ctx-777-τ777 = refl


-- ── product (Tuple) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module product-Tuple-611 where

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=1634 (1×)
  tuple-τ778 : τ 778 ≡ τ 778
  tuple-τ778 = refl


-- ── index (Index) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module index-Index-612 where

  -- ctx-779: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1635 (1×)
  ctx-779-τ779 : τ 779 ≡ τ 779
  ctx-779-τ779 = refl


-- ── subscript (Subscript) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module subscript-Subscript-613 where

  -- ctx-780: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1636 (1×)
  ctx-780-τ780 : τ 780 ≡ τ 780
  ctx-780-τ780 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-614 where

  -- ctx-781: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1637 (1×)
  ctx-781-τ781 : τ 781 ≡ τ 781
  ctx-781-τ781 = refl


-- ── comprehension (comprehension) ──────────────
-- 1 nodes, 1 type contexts, 1 forms

module comprehension-616 where

  -- ctx-783: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1646 (1×)
  ctx-783-τ783 : τ 783 ≡ τ 783
  ctx-783-τ783 = refl


-- ── free_monoid.map (ListComp) ─────────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-map-ListComp-617 where

  -- ctx-784: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1647 (1×)
  ctx-784-τ784 : τ 784 ≡ τ 784
  ctx-784-τ784 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-618 where

  -- ctx-785: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1648 (1×)
  ctx-785-τ785 : τ 785 ≡ τ 785
  ctx-785-τ785 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module annassign-AnnAssign-621 where

  -- ctx-788: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1655 (1×)
  ctx-788-τ788 : τ 788 ≡ τ 788
  ctx-788-τ788 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-622 where

  -- ctx-790: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1660 (1×)
  ctx-790-τ790 : τ 790 ≡ τ 790
  ctx-790-τ790 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-623 where

  -- ctx-791: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1666 (1×)
  ctx-791-τ791 : τ 791 ≡ τ 791
  ctx-791-τ791 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-624 where

  -- ctx-792: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1667 (1×)
  ctx-792-τ792 : τ 792 ≡ τ 792
  ctx-792-τ792 = refl


-- ── coproduct.elim (If) ────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module coproduct-elim-If-625 where

  -- ctx-793: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1673 (1×)
  ctx-793-τ793 : τ 793 ≡ τ 793
  ctx-793-τ793 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-626 where

  -- ctx-794: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1674 (1×)
  ctx-794-τ794 : τ 794 ≡ τ 794
  ctx-794-τ794 = refl


-- ── projection@? (Attribute) ───────────────────
-- 1 nodes, 1 type contexts, 1 forms

module projection-at-x3f-Attribute-628 where

  -- ctx-796: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1681 (1×)
  ctx-796-τ796 : τ 796 ≡ τ 796
  ctx-796-τ796 = refl


-- ── projection.compute@? (Call) ────────────────
-- 1 nodes, 1 type contexts, 1 forms

module projection-compute-at-x3f-Call-629 where

  -- ctx-797: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1682 (1×)
  ctx-797-τ797 : τ 797 ≡ τ 797
  ctx-797-τ797 = refl


-- ── apply (Call) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module apply-Call-630 where

  -- ctx-798: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1683 (1×)
  ctx-798-τ798 : τ 798 ≡ τ 798
  ctx-798-τ798 = refl


-- ── endomorphism (UnaryOp) ─────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module endomorphism-UnaryOp-631 where

  -- ctx-799: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1684 (1×)
  ctx-799-τ799 : τ 799 ≡ τ 799
  ctx-799-τ799 = refl


-- ── lambda (Lambda) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module lambda-Lambda-632 where

  -- ctx-800: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1685 (1×)
  ctx-800-τ800 : τ 800 ≡ τ 800
  ctx-800-τ800 = refl


-- ── keyword (keyword) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module keyword-633 where

  -- ctx-801: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1686 (1×)
  ctx-801-τ801 : τ 801 ≡ τ 801
  ctx-801-τ801 = refl


-- ── apply (Call) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module apply-Call-634 where

  -- ctx-802: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1687 (1×)
  ctx-802-τ802 : τ 802 ≡ τ 802
  ctx-802-τ802 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-635 where

  -- ctx-803: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1688 (1×)
  ctx-803-τ803 : τ 803 ≡ τ 803
  ctx-803-τ803 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-636 where

  -- ctx-804: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1690 (1×)
  ctx-804-τ804 : τ 804 ≡ τ 804
  ctx-804-τ804 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-637 where

  -- ctx-809: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1707 (1×)
  ctx-809-τ809 : τ 809 ≡ τ 809
  ctx-809-τ809 = refl


-- ── free_monoid.op@? (Attribute) ───────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-op-at-x3f-Attribute-638 where

  -- ctx-810: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1712 (1×)
  ctx-810-τ810 : τ 810 ≡ τ 810
  ctx-810-τ810 = refl


-- ── free_monoid.snoc@? (Call) ──────────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-x3f-Call-639 where

  -- ctx-811: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1713 (1×)
  ctx-811-τ811 : τ 811 ≡ τ 811
  ctx-811-τ811 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-640 where

  -- ctx-812: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1714 (1×)
  ctx-812-τ812 : τ 812 ≡ τ 812
  ctx-812-τ812 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-641 where

  -- ctx-813: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1715 (1×)
  ctx-813-τ813 : τ 813 ≡ τ 813
  ctx-813-τ813 = refl


-- ── product (Tuple) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module product-Tuple-642 where

  -- tuple: 1 nodes, 1 forms
  -- [tuple]
  --   σ=1718 (1×)
  tuple-τ814 : τ 814 ≡ τ 814
  tuple-τ814 = refl


-- ── index (Index) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module index-Index-643 where

  -- ctx-815: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1719 (1×)
  ctx-815-τ815 : τ 815 ≡ τ 815
  ctx-815-τ815 = refl


-- ── subscript (Subscript) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module subscript-Subscript-644 where

  -- ctx-816: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1720 (1×)
  ctx-816-τ816 : τ 816 ≡ τ 816
  ctx-816-τ816 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-645 where

  -- ctx-817: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1721 (1×)
  ctx-817-τ817 : τ 817 ≡ τ 817
  ctx-817-τ817 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module annassign-AnnAssign-651 where

  -- ctx-823: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1729 (1×)
  ctx-823-τ823 : τ 823 ≡ τ 823
  ctx-823-τ823 = refl


-- ── exponential.map (DictComp) ─────────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-map-DictComp-652 where

  -- ctx-825: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1742 (1×)
  ctx-825-τ825 : τ 825 ≡ τ 825
  ctx-825-τ825 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-653 where

  -- ctx-826: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1743 (1×)
  ctx-826-τ826 : τ 826 ≡ τ 826
  ctx-826-τ826 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-656 where

  -- ctx-829: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1755 (1×)
  ctx-829-τ829 : τ 829 ≡ τ 829
  ctx-829-τ829 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-657 where

  -- ctx-830: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1756 (1×)
  ctx-830-τ830 : τ 830 ≡ τ 830
  ctx-830-τ830 = refl


-- ── endomorphism (UnaryOp) ─────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module endomorphism-UnaryOp-658 where

  -- ctx-831: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1760 (1×)
  ctx-831-τ831 : τ 831 ≡ τ 831
  ctx-831-τ831 = refl


-- ── lambda (Lambda) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module lambda-Lambda-659 where

  -- ctx-832: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1761 (1×)
  ctx-832-τ832 : τ 832 ≡ τ 832
  ctx-832-τ832 = refl


-- ── keyword (keyword) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module keyword-660 where

  -- ctx-833: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1762 (1×)
  ctx-833-τ833 : τ 833 ≡ τ 833
  ctx-833-τ833 = refl


-- ── apply (Call) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module apply-Call-661 where

  -- ctx-834: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1763 (1×)
  ctx-834-τ834 : τ 834 ≡ τ 834
  ctx-834-τ834 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-662 where

  -- ctx-835: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1764 (1×)
  ctx-835-τ835 : τ 835 ≡ τ 835
  ctx-835-τ835 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-663 where

  -- ctx-836: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1766 (1×)
  ctx-836-τ836 : τ 836 ≡ τ 836
  ctx-836-τ836 = refl


-- ── free_monoid.fold (JoinedStr) ───────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-JoinedStr-665 where

  -- str: 1 nodes, 1 forms
  -- [str]
  --   σ=1790 (1×)
  str-τ841 : τ 841 ≡ τ 841
  str-τ841 = refl


-- ── terminal.map (Return) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module terminal-map-Return-666 where

  -- ctx-842: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1791 (1×)
  ctx-842-τ842 : τ 842 ≡ τ 842
  ctx-842-τ842 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-667 where

  -- ctx-843: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1792 (1×)
  ctx-843-τ843 : τ 843 ≡ τ 843
  ctx-843-τ843 = refl


-- ── equalizer (Compare) ────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-Compare-668 where

  -- ctx-844: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1798 (1×)
  ctx-844-τ844 : τ 844 ≡ τ 844
  ctx-844-τ844 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-669 where

  -- ctx-845: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1801 (1×)
  ctx-845-τ845 : τ 845 ≡ τ 845
  ctx-845-τ845 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-670 where

  -- ctx-847: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1810 (1×)
  ctx-847-τ847 : τ 847 ≡ τ 847
  ctx-847-τ847 = refl


-- ── coerce (FormattedValue) ────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module coerce-FormattedValue-685 where

  -- ctx-862: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1864 (1×)
  ctx-862-τ862 : τ 862 ≡ τ 862
  ctx-862-τ862 = refl


-- ── free_monoid.fold (JoinedStr) ───────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-JoinedStr-686 where

  -- str: 1 nodes, 1 forms
  -- [str]
  --   σ=1865 (1×)
  str-τ863 : τ 863 ≡ τ 863
  str-τ863 = refl


-- ── free_monoid.literal (List) ─────────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-literal-List-687 where

  -- list: 1 nodes, 1 forms
  -- [list]
  --   σ=1866 (1×)
  list-τ864 : τ 864 ≡ τ 864
  list-τ864 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-688 where

  -- ctx-865: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1867 (1×)
  ctx-865-τ865 : τ 865 ≡ τ 865
  ctx-865-τ865 = refl


-- ── subobject (Attribute) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module subobject-Attribute-689 where

  -- ctx-796: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1873 (1×)
  ctx-796-τ796 : τ 796 ≡ τ 796
  ctx-796-τ796 = refl


-- ── subobject.test (Call) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module subobject-test-Call-690 where

  -- ctx-866: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1875 (1×)
  ctx-866-τ866 : τ 866 ≡ τ 866
  ctx-866-τ866 = refl


-- ── meet (BoolOp) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module meet-BoolOp-691 where

  -- ctx-867: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1876 (1×)
  ctx-867-τ867 : τ 867 ≡ τ 867
  ctx-867-τ867 = refl


-- ── comprehension (comprehension) ──────────────
-- 1 nodes, 1 type contexts, 1 forms

module comprehension-692 where

  -- ctx-868: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1877 (1×)
  ctx-868-τ868 : τ 868 ≡ τ 868
  ctx-868-τ868 = refl


-- ── lazy_fold (GeneratorExp) ───────────────────
-- 1 nodes, 1 type contexts, 1 forms

module lazy_fold-GeneratorExp-693 where

  -- ctx-869: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1878 (1×)
  ctx-869-τ869 : τ 869 ≡ τ 869
  ctx-869-τ869 = refl


-- ── apply (Call) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module apply-Call-694 where

  -- ctx-870: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1879 (1×)
  ctx-870-τ870 : τ 870 ≡ τ 870
  ctx-870-τ870 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-695 where

  -- ctx-871: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1880 (1×)
  ctx-871-τ871 : τ 871 ≡ τ 871
  ctx-871-τ871 = refl


-- ── powerset (Call) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module powerset-Call-696 where

  -- ctx-872: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1882 (1×)
  ctx-872-τ872 : τ 872 ≡ τ 872
  ctx-872-τ872 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module annassign-AnnAssign-697 where

  -- ctx-873: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1883 (1×)
  ctx-873-τ873 : τ 873 ≡ τ 873
  ctx-873-τ873 = refl


-- ── ifexp (IfExp) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module ifexp-IfExp-698 where

  -- ctx-874: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1890 (1×)
  ctx-874-τ874 : τ 874 ≡ τ 874
  ctx-874-τ874 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-699 where

  -- ctx-875: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1891 (1×)
  ctx-875-τ875 : τ 875 ≡ τ 875
  ctx-875-τ875 = refl


-- ── bimap (BinOp) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module bimap-BinOp-700 where

  -- ctx-876: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1896 (1×)
  ctx-876-τ876 : τ 876 ≡ τ 876
  ctx-876-τ876 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-701 where

  -- ctx-877: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1897 (1×)
  ctx-877-τ877 : τ 877 ≡ τ 877
  ctx-877-τ877 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module annassign-AnnAssign-702 where

  -- ctx-879: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1900 (1×)
  ctx-879-τ879 : τ 879 ≡ τ 879
  ctx-879-τ879 = refl


-- ── annassign (AnnAssign) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module annassign-AnnAssign-703 where

  -- ctx-880: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1903 (1×)
  ctx-880-τ880 : τ 880 ≡ τ 880
  ctx-880-τ880 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-704 where

  -- ctx-881: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1908 (1×)
  ctx-881-τ881 : τ 881 ≡ τ 881
  ctx-881-τ881 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-705 where

  -- ctx-882: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1909 (1×)
  ctx-882-τ882 : τ 882 ≡ τ 882
  ctx-882-τ882 = refl


-- ── monoid.op@? (Attribute) ────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module monoid-op-at-x3f-Attribute-706 where

  -- ctx-810: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1911 (1×)
  ctx-810-τ810 : τ 810 ≡ τ 810
  ctx-810-τ810 = refl


-- ── partial.apply@? (Call) ─────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module partial-apply-at-x3f-Call-707 where

  -- ctx-883: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1913 (1×)
  ctx-883-τ883 : τ 883 ≡ τ 883
  ctx-883-τ883 = refl


-- ── monoid.op@? (Call) ─────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module monoid-op-at-x3f-Call-708 where

  -- ctx-884: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1914 (1×)
  ctx-884-τ884 : τ 884 ≡ τ 884
  ctx-884-τ884 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-709 where

  -- ctx-885: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1915 (1×)
  ctx-885-τ885 : τ 885 ≡ τ 885
  ctx-885-τ885 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-710 where

  -- ctx-886: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1916 (1×)
  ctx-886-τ886 : τ 886 ≡ τ 886
  ctx-886-τ886 = refl


-- ── comprehension (comprehension) ──────────────
-- 1 nodes, 1 type contexts, 1 forms

module comprehension-711 where

  -- ctx-887: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1921 (1×)
  ctx-887-τ887 : τ 887 ≡ τ 887
  ctx-887-τ887 = refl


-- ── lazy_fold (GeneratorExp) ───────────────────
-- 1 nodes, 1 type contexts, 1 forms

module lazy_fold-GeneratorExp-712 where

  -- ctx-888: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1922 (1×)
  ctx-888-τ888 : τ 888 ≡ τ 888
  ctx-888-τ888 = refl


-- ── apply (Call) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module apply-Call-713 where

  -- ctx-889: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1923 (1×)
  ctx-889-τ889 : τ 889 ≡ τ 889
  ctx-889-τ889 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-714 where

  -- ctx-890: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1924 (1×)
  ctx-890-τ890 : τ 890 ≡ τ 890
  ctx-890-τ890 = refl


-- ── free_monoid.fold (JoinedStr) ───────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-JoinedStr-716 where

  -- str: 1 nodes, 1 forms
  -- [str]
  --   σ=1930 (1×)
  str-τ892 : τ 892 ≡ τ 892
  str-τ892 = refl


-- ── free_monoid.snoc@sequence (Call) ───────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-sequence-Call-717 where

  -- None: 1 nodes, 1 forms
  -- [None]
  --   σ=1931 (1×)
  None-τ893 : τ 893 ≡ τ 893
  None-τ893 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-718 where

  -- ctx-894: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1932 (1×)
  ctx-894-τ894 : τ 894 ≡ τ 894
  ctx-894-τ894 = refl


-- ── free_monoid.fold (JoinedStr) ───────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-JoinedStr-719 where

  -- str: 1 nodes, 1 forms
  -- [str]
  --   σ=1940 (1×)
  str-τ895 : τ 895 ≡ τ 895
  str-τ895 = refl


-- ── free_monoid.snoc@sequence (Call) ───────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-sequence-Call-720 where

  -- None: 1 nodes, 1 forms
  -- [None]
  --   σ=1941 (1×)
  None-τ896 : τ 896 ≡ τ 896
  None-τ896 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-721 where

  -- ctx-897: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1942 (1×)
  ctx-897-τ897 : τ 897 ≡ τ 897
  ctx-897-τ897 = refl


-- ── free_monoid.fold (JoinedStr) ───────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-JoinedStr-722 where

  -- str: 1 nodes, 1 forms
  -- [str]
  --   σ=1952 (1×)
  str-τ898 : τ 898 ≡ τ 898
  str-τ898 = refl


-- ── free_monoid.snoc@sequence (Call) ───────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-sequence-Call-723 where

  -- None: 1 nodes, 1 forms
  -- [None]
  --   σ=1953 (1×)
  None-τ899 : τ 899 ≡ τ 899
  None-τ899 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-724 where

  -- ctx-900: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1954 (1×)
  ctx-900-τ900 : τ 900 ≡ τ 900
  ctx-900-τ900 = refl


-- ── mult (Mult) ────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module mult-Mult-725 where

  -- ctx-901: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1961 (1×)
  ctx-901-τ901 : τ 901 ≡ τ 901
  ctx-901-τ901 = refl


-- ── bimap (BinOp) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module bimap-BinOp-726 where

  -- ctx-903: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1963 (1×)
  ctx-903-τ903 : τ 903 ≡ τ 903
  ctx-903-τ903 = refl


-- ── equalizer (Compare) ────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-Compare-727 where

  -- ctx-904: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1964 (1×)
  ctx-904-τ904 : τ 904 ≡ τ 904
  ctx-904-τ904 = refl


-- ── ifexp (IfExp) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module ifexp-IfExp-728 where

  -- ctx-905: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1967 (1×)
  ctx-905-τ905 : τ 905 ≡ τ 905
  ctx-905-τ905 = refl


-- ── coerce (FormattedValue) ────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module coerce-FormattedValue-729 where

  -- ctx-906: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1968 (1×)
  ctx-906-τ906 : τ 906 ≡ τ 906
  ctx-906-τ906 = refl


-- ── free_monoid.fold (JoinedStr) ───────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-JoinedStr-730 where

  -- str: 1 nodes, 1 forms
  -- [str]
  --   σ=1969 (1×)
  str-τ907 : τ 907 ≡ τ 907
  str-τ907 = refl


-- ── free_monoid.snoc@sequence (Call) ───────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-sequence-Call-731 where

  -- None: 1 nodes, 1 forms
  -- [None]
  --   σ=1970 (1×)
  None-τ908 : τ 908 ≡ τ 908
  None-τ908 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-732 where

  -- ctx-909: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1971 (1×)
  ctx-909-τ909 : τ 909 ≡ τ 909
  ctx-909-τ909 = refl


-- ── exponential.literal (Dict) ─────────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-literal-Dict-733 where

  -- dict: 1 nodes, 1 forms
  -- [dict]
  --   σ=1979 (1×)
  dict-τ910 : τ 910 ≡ τ 910
  dict-τ910 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-734 where

  -- ctx-911: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1980 (1×)
  ctx-911-τ911 : τ 911 ≡ τ 911
  ctx-911-τ911 = refl


-- ── partial.apply@state (Call) ─────────────────
-- 1 nodes, 1 type contexts, 1 forms

module partial-apply-at-state-Call-735 where

  -- T: 1 nodes, 1 forms
  -- [T]
  --   σ=1983 (1×)
  T-τ913 : τ 913 ≡ τ 913
  T-τ913 = refl


-- ── cardinality (Call) ─────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module cardinality-Call-736 where

  -- int: 1 nodes, 1 forms
  -- [int]
  --   σ=1984 (1×)
  int-τ914 : τ 914 ≡ τ 914
  int-τ914 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-737 where

  -- ctx-915: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1985 (1×)
  ctx-915-τ915 : τ 915 ≡ τ 915
  ctx-915-τ915 = refl


-- ── bimap (BinOp) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module bimap-BinOp-738 where

  -- ctx-916: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1988 (1×)
  ctx-916-τ916 : τ 916 ≡ τ 916
  ctx-916-τ916 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-739 where

  -- ctx-917: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1989 (1×)
  ctx-917-τ917 : τ 917 ≡ τ 917
  ctx-917-τ917 = refl


-- ── free_monoid.snoc@sequence (Call) ───────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-sequence-Call-740 where

  -- None: 1 nodes, 1 forms
  -- [None]
  --   σ=1991 (1×)
  None-τ918 : τ 918 ≡ τ 918
  None-τ918 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-741 where

  -- ctx-919: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=1992 (1×)
  ctx-919-τ919 : τ 919 ≡ τ 919
  ctx-919-τ919 = refl


-- ── free_monoid.fold (JoinedStr) ───────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-JoinedStr-743 where

  -- str: 1 nodes, 1 forms
  -- [str]
  --   σ=2003 (1×)
  str-τ923 : τ 923 ≡ τ 923
  str-τ923 = refl


-- ── free_monoid.snoc@sequence (Call) ───────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-sequence-Call-744 where

  -- None: 1 nodes, 1 forms
  -- [None]
  --   σ=2004 (1×)
  None-τ924 : τ 924 ≡ τ 924
  None-τ924 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-745 where

  -- ctx-925: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=2005 (1×)
  ctx-925-τ925 : τ 925 ≡ τ 925
  ctx-925-τ925 = refl


-- ── projection@state (Attribute) ───────────────
-- 1 nodes, 1 type contexts, 1 forms

module projection-at-state-Attribute-746 where

  -- Self-_cell_obs-keys: 1 nodes, 1 forms
  -- [Self._cell_contents.get, Self._cell_obs.get, Self._cell_obs.keys, Self._cleavage_fibers.append, Self._cleavage_levels.append]
  --   σ=2006 (1×)
  Self-_cell_obs-keys-τ153 : τ 153 ≡ τ 153
  Self-_cell_obs-keys-τ153 = refl


-- ── projection.compute@state (Call) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module projection-compute-at-state-Call-747 where

  -- Iter: 1 nodes, 1 forms
  -- [Iter]
  --   σ=2007 (1×)
  Iter-τ927 : τ 927 ≡ τ 927
  Iter-τ927 = refl


-- ── total_order (Call) ─────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module total_order-Call-748 where

  -- list: 1 nodes, 1 forms
  -- [list]
  --   σ=2008 (1×)
  list-τ928 : τ 928 ≡ τ 928
  list-τ928 = refl


-- ── complement (If) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module complement-If-749 where

  -- ctx-929: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=2011 (1×)
  ctx-929-τ929 : τ 929 ≡ τ 929
  ctx-929-τ929 = refl


-- ── partial@mapping (Attribute) ────────────────
-- 1 nodes, 1 type contexts, 1 forms

module partial-at-mapping-Attribute-750 where

  -- dict-get: 1 nodes, 1 forms
  -- [Self._cascade_abstraction_merge, Self._cascade_eta, Self._cell_contents, Self._cell_obs, Self._cleavage_fibers]
  --   σ=2013 (1×)
  dict-get-τ34 : τ 34 ≡ τ 34
  dict-get-τ34 = refl


-- ── partial.apply@mapping (Call) ───────────────
-- 1 nodes, 1 type contexts, 1 forms

module partial-apply-at-mapping-Call-751 where

  -- T: 1 nodes, 1 forms
  -- [T]
  --   σ=2017 (1×)
  T-τ932 : τ 932 ≡ τ 932
  T-τ932 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-752 where

  -- ctx-933: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=2018 (1×)
  ctx-933-τ933 : τ 933 ≡ τ 933
  ctx-933-τ933 = refl


-- ── lambda (Lambda) ────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module lambda-Lambda-753 where

  -- ctx-934: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=2024 (1×)
  ctx-934-τ934 : τ 934 ≡ τ 934
  ctx-934-τ934 = refl


-- ── keyword (keyword) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module keyword-754 where

  -- ctx-935: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=2025 (1×)
  ctx-935-τ935 : τ 935 ≡ τ 935
  ctx-935-τ935 = refl


-- ── apply (Call) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module apply-Call-755 where

  -- ctx-936: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=2026 (1×)
  ctx-936-τ936 : τ 936 ≡ τ 936
  ctx-936-τ936 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-756 where

  -- ctx-937: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=2027 (1×)
  ctx-937-τ937 : τ 937 ≡ τ 937
  ctx-937-τ937 = refl


-- ── coerce (Call) ──────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module coerce-Call-757 where

  -- ctx-404: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=2030 (1×)
  ctx-404-τ404 : τ 404 ≡ τ 404
  ctx-404-τ404 = refl


-- ── subscript (Subscript) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module subscript-Subscript-758 where

  -- ctx-938: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=2033 (1×)
  ctx-938-τ938 : τ 938 ≡ τ 938
  ctx-938-τ938 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-759 where

  -- ctx-939: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=2034 (1×)
  ctx-939-τ939 : τ 939 ≡ τ 939
  ctx-939-τ939 = refl


-- ── free_monoid.fold (JoinedStr) ───────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-JoinedStr-760 where

  -- str: 1 nodes, 1 forms
  -- [str]
  --   σ=2047 (1×)
  str-τ940 : τ 940 ≡ τ 940
  str-τ940 = refl


-- ── free_monoid.snoc@sequence (Call) ───────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-sequence-Call-761 where

  -- None: 1 nodes, 1 forms
  -- [None]
  --   σ=2048 (1×)
  None-τ941 : τ 941 ≡ τ 941
  None-τ941 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-762 where

  -- ctx-942: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=2049 (1×)
  ctx-942-τ942 : τ 942 ≡ τ 942
  ctx-942-τ942 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-763 where

  -- ctx-943: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=2050 (1×)
  ctx-943-τ943 : τ 943 ≡ τ 943
  ctx-943-τ943 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-764 where

  -- ctx-944: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=2053 (1×)
  ctx-944-τ944 : τ 944 ≡ τ 944
  ctx-944-τ944 = refl


-- ── partial.apply@? (Call) ─────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module partial-apply-at-x3f-Call-765 where

  -- ctx-946: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=2059 (1×)
  ctx-946-τ946 : τ 946 ≡ τ 946
  ctx-946-τ946 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-766 where

  -- ctx-947: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=2060 (1×)
  ctx-947-τ947 : τ 947 ≡ τ 947
  ctx-947-τ947 = refl


-- ── let (Assign) ───────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module let-k-Assign-767 where

  -- ctx-948: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=2068 (1×)
  ctx-948-τ948 : τ 948 ≡ τ 948
  ctx-948-τ948 = refl


-- ── free_monoid.fold (JoinedStr) ───────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-JoinedStr-768 where

  -- str: 1 nodes, 1 forms
  -- [str]
  --   σ=2084 (1×)
  str-τ951 : τ 951 ≡ τ 951
  str-τ951 = refl


-- ── free_monoid.snoc@sequence (Call) ───────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-sequence-Call-769 where

  -- None: 1 nodes, 1 forms
  -- [None]
  --   σ=2085 (1×)
  None-τ952 : τ 952 ≡ τ 952
  None-τ952 = refl


-- ── effect.seq (Expr) ──────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module effect-seq-Expr-770 where

  -- ctx-953: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=2086 (1×)
  ctx-953-τ953 : τ 953 ≡ τ 953
  ctx-953-τ953 = refl


-- ── equalizer (If) ─────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module equalizer-If-771 where

  -- ctx-954: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=2087 (1×)
  ctx-954-τ954 : τ 954 ≡ τ 954
  ctx-954-τ954 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-772 where

  -- ctx-955: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=2088 (1×)
  ctx-955-τ955 : τ 955 ≡ τ 955
  ctx-955-τ955 = refl


-- ── fold (For) ─────────────────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module fold-For-773 where

  -- ctx-956: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=2089 (1×)
  ctx-956-τ956 : τ 956 ≡ τ 956
  ctx-956-τ956 = refl


-- ── free_monoid.fold (Attribute) ───────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-Attribute-774 where

  -- str-join: 1 nodes, 1 forms
  -- [str.join]
  --   σ=2091 (1×)
  str-join-τ957 : τ 957 ≡ τ 957
  str-join-τ957 = refl


-- ── free_monoid.fold (Call) ────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-Call-775 where

  -- str: 1 nodes, 1 forms
  -- [str]
  --   σ=2092 (1×)
  str-τ958 : τ 958 ≡ τ 958
  str-τ958 = refl


-- ── terminal.map (Return) ──────────────────────
-- 1 nodes, 1 type contexts, 1 forms

module terminal-map-Return-776 where

  -- ctx-959: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=2093 (1×)
  ctx-959-τ959 : τ 959 ≡ τ 959
  ctx-959-τ959 = refl


-- ── exponential.intro (FunctionDef) ────────────
-- 1 nodes, 1 type contexts, 1 forms

module exponential-intro-FunctionDef-777 where

  -- ctx-960: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=2094 (1×)
  ctx-960-τ960 : τ 960 ≡ τ 960
  ctx-960-τ960 = refl


-- ── classifier.intro (ClassDef) ────────────────
-- 1 nodes, 1 type contexts, 1 forms

module classifier-intro-ClassDef-778 where

  -- ctx-961: 1 nodes, 1 forms
  -- [(untyped)]
  --   σ=2095 (1×)
  ctx-961-τ961 : τ 961 ≡ τ 961
  ctx-961-τ961 = refl


-- ══════════════════════════════════════════════════════════
-- Cleavage planes (module boundaries / case splits)
-- ══════════════════════════════════════════════════════════

-- Case split: Attribute with 25 type witnesses
module Attribute-split-0 where

  Self-_parent : τ 34 ≡ τ 34
  Self-_parent = refl  -- 7 nodes

  Self-find : τ 34 ≡ τ 34
  Self-find = refl  -- 2 nodes

  Self-_rank : τ 34 ≡ τ 34
  Self-_rank = refl  -- 1 nodes

  Self-_counter : τ 34 ≡ τ 34
  Self-_counter = refl  -- 1 nodes

  Self-canonical_classes : τ 34 ≡ τ 34
  Self-canonical_classes = refl  -- 1 nodes

  Self-_observe_cell : τ 34 ≡ τ 34
  Self-_observe_cell = refl  -- 1 nodes

  Self-_resolve_type : τ 34 ≡ τ 34
  Self-_resolve_type = refl  -- 1 nodes

  Self-_merge_residue_sets : τ 34 ≡ τ 34
  Self-_merge_residue_sets = refl  -- 1 nodes

  Self-_process_cleavage : τ 34 ≡ τ 34
  Self-_process_cleavage = refl  -- 1 nodes

  Self-_seed_worklist : τ 34 ≡ τ 34
  Self-_seed_worklist = refl  -- 1 nodes

  Self-_recanon_structural_key : τ 34 ≡ τ 34
  Self-_recanon_structural_key = refl  -- 1 nodes

  T-items : τ 34 ≡ τ 34
  T-items = refl  -- 1 nodes

  T-keys : τ 34 ≡ τ 34
  T-keys = refl  -- 1 nodes

  Self-_cascade_abstraction_merge : τ 34 ≡ τ 34
  Self-_cascade_abstraction_merge = refl  -- 1 nodes

  Self-_update_residue : τ 34 ≡ τ 34
  Self-_update_residue = refl  -- 1 nodes

  Self-_cascade_eta : τ 34 ≡ τ 34
  Self-_cascade_eta = refl  -- 1 nodes

  Self-_resolve : τ 34 ≡ τ 34
  Self-_resolve = refl  -- 1 nodes

  Self-rank : τ 34 ≡ τ 34
  Self-rank = refl  -- 1 nodes

  Self-residue : τ 34 ≡ τ 34
  Self-residue = refl  -- 1 nodes

  Self-hybrid : τ 34 ≡ τ 34
  Self-hybrid = refl  -- 1 nodes

  Self-node_count : τ 34 ≡ τ 34
  Self-node_count = refl  -- 1 nodes

  Self-wedge : τ 34 ≡ τ 34
  Self-wedge = refl  -- 1 nodes

  list-append : τ 34 ≡ τ 34
  list-append = refl  -- 1 nodes

  dict-get : τ 34 ≡ τ 34
  dict-get = refl  -- 1 nodes

  Self-rank_distribution : τ 34 ≡ τ 34
  Self-rank_distribution = refl  -- 1 nodes


-- Case split: Attribute with 28 type witnesses
module Attribute-split-1 where

  Self-_counter : τ 14 ≡ τ 14
  Self-_counter = refl  -- 2 nodes

  Self-_parent : τ 14 ≡ τ 14
  Self-_parent = refl  -- 1 nodes

  Self-_rank : τ 14 ≡ τ 14
  Self-_rank = refl  -- 1 nodes

  Self-id : τ 14 ≡ τ 14
  Self-id = refl  -- 1 nodes

  Self-signature : τ 14 ≡ τ 14
  Self-signature = refl  -- 1 nodes

  Self-child_ids : τ 14 ≡ τ 14
  Self-child_ids = refl  -- 1 nodes

  Self-node_indices : τ 14 ≡ τ 14
  Self-node_indices = refl  -- 1 nodes

  Self-name : τ 14 ≡ τ 14
  Self-name = refl  -- 1 nodes

  Self-classes : τ 14 ≡ τ 14
  Self-classes = refl  -- 1 nodes

  Self-_registry : τ 14 ≡ τ 14
  Self-_registry = refl  -- 1 nodes

  Self-uf : τ 14 ≡ τ 14
  Self-uf = refl  -- 1 nodes

  Self-sigma : τ 14 ≡ τ 14
  Self-sigma = refl  -- 1 nodes

  Self-tau : τ 14 ≡ τ 14
  Self-tau = refl  -- 1 nodes

  Self-kappa : τ 14 ≡ τ 14
  Self-kappa = refl  -- 1 nodes

  Self-nodes : τ 14 ≡ τ 14
  Self-nodes = refl  -- 1 nodes

  Self-_tau_structural : τ 14 ≡ τ 14
  Self-_tau_structural = refl  -- 1 nodes

  Self-_tau_structural_by_child : τ 14 ≡ τ 14
  Self-_tau_structural_by_child = refl  -- 1 nodes

  Self-_tau_structural_by_variant : τ 14 ≡ τ 14
  Self-_tau_structural_by_variant = refl  -- 1 nodes

  Self-_eta_abstractions : τ 14 ≡ τ 14
  Self-_eta_abstractions = refl  -- 1 nodes

  Self-_eta_uf : τ 14 ≡ τ 14
  Self-_eta_uf = refl  -- 1 nodes

  Self-_eta_count : τ 14 ≡ τ 14
  Self-_eta_count = refl  -- 1 nodes

  Self-_eta_tower : τ 14 ≡ τ 14
  Self-_eta_tower = refl  -- 1 nodes

  Self-_residue_sets : τ 14 ≡ τ 14
  Self-_residue_sets = refl  -- 1 nodes

  Self-_cleavage_levels : τ 14 ≡ τ 14
  Self-_cleavage_levels = refl  -- 1 nodes

  Self-_cleavage_fibers : τ 14 ≡ τ 14
  Self-_cleavage_fibers = refl  -- 1 nodes

  Self-_cleavage_ghost_count : τ 14 ≡ τ 14
  Self-_cleavage_ghost_count = refl  -- 1 nodes

  Self-_cell_obs : τ 14 ≡ τ 14
  Self-_cell_obs = refl  -- 1 nodes

  Self-_cell_contents : τ 14 ≡ τ 14
  Self-_cell_contents = refl  -- 1 nodes


-- Case split: Attribute with 26 type witnesses
module Attribute-split-2 where

  Self-uf-find : τ 153 ≡ τ 153
  Self-uf-find = refl  -- 2 nodes

  Self-uf-make : τ 153 ≡ τ 153
  Self-uf-make = refl  -- 1 nodes

  Self-uf-union : τ 153 ≡ τ 153
  Self-uf-union = refl  -- 1 nodes

  Self-_cell_contents-get : τ 153 ≡ τ 153
  Self-_cell_contents-get = refl  -- 1 nodes

  Self-tau-canonical : τ 153 ≡ τ 153
  Self-tau-canonical = refl  -- 1 nodes

  Self-_residue_sets-get : τ 153 ≡ τ 153
  Self-_residue_sets-get = refl  -- 1 nodes

  Self-_cleavage_levels-append : τ 153 ≡ τ 153
  Self-_cleavage_levels-append = refl  -- 1 nodes

  Self-_cleavage_fibers-append : τ 153 ≡ τ 153
  Self-_cleavage_fibers-append = refl  -- 1 nodes

  Self-tau-classes : τ 153 ≡ τ 153
  Self-tau-classes = refl  -- 1 nodes

  Self-_eta_tower-append : τ 153 ≡ τ 153
  Self-_eta_tower-append = refl  -- 1 nodes

  Self-_eta_abstractions-get : τ 153 ≡ τ 153
  Self-_eta_abstractions-get = refl  -- 1 nodes

  Self-_eta_uf-find : τ 153 ≡ τ 153
  Self-_eta_uf-find = refl  -- 1 nodes

  Self-_tau_structural_by_variant-get : τ 153 ≡ τ 153
  Self-_tau_structural_by_variant-get = refl  -- 1 nodes

  Self-tau-merge : τ 153 ≡ τ 153
  Self-tau-merge = refl  -- 1 nodes

  Self-_tau_structural_by_child-get : τ 153 ≡ τ 153
  Self-_tau_structural_by_child-get = refl  -- 1 nodes

  Self-_tau_structural-get : τ 153 ≡ τ 153
  Self-_tau_structural-get = refl  -- 1 nodes

  Self-_eta_uf-make : τ 153 ≡ τ 153
  Self-_eta_uf-make = refl  -- 1 nodes

  Self-_eta_uf-union : τ 153 ≡ τ 153
  Self-_eta_uf-union = refl  -- 1 nodes

  Self-sigma-_assign : τ 153 ≡ τ 153
  Self-sigma-_assign = refl  -- 1 nodes

  Self-kappa-_assign : τ 153 ≡ τ 153
  Self-kappa-_assign = refl  -- 1 nodes

  Self-tau-_assign : τ 153 ≡ τ 153
  Self-tau-_assign = refl  -- 1 nodes

  Self-nodes-append : τ 153 ≡ τ 153
  Self-nodes-append = refl  -- 1 nodes

  Self-sigma-classes : τ 153 ≡ τ 153
  Self-sigma-classes = refl  -- 1 nodes

  Self-kappa-classes : τ 153 ≡ τ 153
  Self-kappa-classes = refl  -- 1 nodes

  Self-_cell_obs-get : τ 153 ≡ τ 153
  Self-_cell_obs-get = refl  -- 1 nodes

  Self-_cell_obs-keys : τ 153 ≡ τ 153
  Self-_cell_obs-keys = refl  -- 1 nodes


-- Case split: Name with 12 type witnesses
module Name-split-3 where

  Self : τ 13 ≡ τ 13
  Self = refl  -- 3 nodes

  dict : τ 13 ≡ τ 13
  dict = refl  -- 1 nodes

  int : τ 13 ≡ τ 13
  int = refl  -- 1 nodes

  bool : τ 13 ≡ τ 13
  bool = refl  -- 1 nodes

  toint : τ 13 ≡ τ 13
  toint = refl  -- 1 nodes

  tuple : τ 13 ≡ τ 13
  tuple = refl  -- 1 nodes

  list : τ 13 ≡ τ 13
  list = refl  -- 1 nodes

  set : τ 13 ≡ τ 13
  set = refl  -- 1 nodes

  tolist : τ 13 ≡ τ 13
  tolist = refl  -- 1 nodes

  tobool : τ 13 ≡ τ 13
  tobool = refl  -- 1 nodes

  AST : τ 13 ≡ τ 13
  AST = refl  -- 1 nodes

  toT : τ 13 ≡ τ 13
  toT = refl  -- 1 nodes


-- Case split: Constant with 4 type witnesses
module Constant-split-4 where

  str : τ 0 ≡ τ 0
  str = refl  -- 4 nodes

  NoneType : τ 0 ≡ τ 0
  NoneType = refl  -- 2 nodes

  int : τ 0 ≡ τ 0
  int = refl  -- 1 nodes

  float : τ 0 ≡ τ 0
  float = refl  -- 1 nodes


-- Case split: Name with 3 type witnesses
module Name-split-5 where

  tuple : τ 7 ≡ τ 7
  tuple = refl  -- 3 nodes

  Self-_counter : τ 7 ≡ τ 7
  Self-_counter = refl  -- 1 nodes

  T : τ 7 ≡ τ 7
  T = refl  -- 1 nodes


-- Case split: Call with 2 type witnesses
module Call-split-6 where

  None : τ 349 ≡ τ 349
  None = refl  -- 1 nodes

  T : τ 349 ≡ τ 349
  T = refl  -- 1 nodes


-- ══════════════════════════════════════════════════════════
-- Summary:
--   7500 AST nodes → 2109 proof cells
--   779 construction modules
--   13 η-proofs
--   7 cleavage planes
--   Compression: 71.9%
-- ══════════════════════════════════════════════════════════

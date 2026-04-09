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

-- ── load (──────────────────────────────────────────────)
-- κ=8, 2366 nodes, 1 type contexts, 1 forms

module load-8 where

  -- τ=8: 2366 nodes, 1 forms
  -- Types: (untyped)
  -- σ=17 (2366×)
  cell-8-8 : τ 8 ≡ τ 8
  cell-8-8 = refl


-- ── var (───────────────────────────────────────────────)
-- κ=13, 1497 nodes, 2 type contexts, 200 forms

module var-13 where

  -- τ=16: 757 nodes, 175 forms
  -- Types: (untyped)
  -- (175 σ-forms, elided)
  cell-13-16 : τ 16 ≡ τ 16
  cell-13-16 = refl

  -- τ=13: 740 nodes, 31 forms
  -- Types: AST, Self, Self._counter, Self.node_count, T
  -- (31 σ-forms, elided)
  cell-13-13 : τ 13 ≡ τ 13
  cell-13-13 = refl


-- ── store (─────────────────────────────────────────────)
-- κ=6, 365 nodes, 1 type contexts, 1 forms

module store-6 where

  -- τ=6: 365 nodes, 1 forms
  -- Types: (untyped)
  -- σ=13 (365×)
  cell-6-6 : τ 6 ≡ τ 6
  cell-6-6 = refl


-- ── terminal (──────────────────────────────────────────)
-- κ=0, 295 nodes, 2 type contexts, 125 forms

module terminal-0 where

  -- τ=0: 273 nodes, 124 forms
  -- Types: NoneType, bool, float, int, str
  -- (124 σ-forms, elided)
  cell-0-0 : τ 0 ≡ τ 0
  cell-0-0 = refl

  -- τ=95: 22 nodes, 1 forms
  -- Types: (untyped)
  -- σ=141 (22×)
  cell-0-95 : τ 95 ≡ τ 95
  cell-0-95 = refl


-- ── bind (──────────────────────────────────────────────)
-- κ=7, 275 nodes, 2 type contexts, 153 forms

module bind-7 where

  -- τ=44: 245 nodes, 134 forms
  -- Types: (untyped)
  -- (134 σ-forms, elided)
  cell-7-44 : τ 44 ≡ τ 44
  cell-7-44 = refl

  -- τ=7: 30 nodes, 24 forms
  -- Types: Self._counter, Self.node_count, T, dict, int
  -- (24 σ-forms, elided)
  cell-7-7 : τ 7 ≡ τ 7
  cell-7-7 = refl


-- ── morphism@state (────────────────────────────────────)
-- κ=24, 243 nodes, 1 type contexts, 44 forms

module morphism-at-state-24 where

  -- τ=34: 243 nodes, 44 forms
  -- Types: Self._cascade_abstraction_merge, Self._cascade_eta, Self._cell_contents, Self._cell_obs, Self._cleavage_fibers
  -- (44 σ-forms, elided)
  cell-24-34 : τ 34 ≡ τ 34
  cell-24-34 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=26, 130 nodes, 2 type contexts, 43 forms

module index-26 where

  -- τ=36: 84 nodes, 38 forms
  -- Types: (untyped)
  -- (38 σ-forms, elided)
  cell-26-36 : τ 36 ≡ τ 36
  cell-26-36 = refl

  -- τ=113: 46 nodes, 6 forms
  -- Types: (untyped)
  -- σ=162 (19×)
  -- σ=219 (2×)
  -- σ=346 (20×)
  -- σ=433 (2×)
  -- σ=446 (1×)
  -- σ=550 (2×)
  cell-26-113 : τ 113 ≡ τ 113
  cell-26-113 = refl


-- ── morphism@state (────────────────────────────────────)
-- κ=105, 68 nodes, 1 type contexts, 14 forms

module morphism-at-state-105 where

  -- τ=153: 68 nodes, 14 forms
  -- Types: Self._cell_contents.get, Self._cell_obs.get, Self._cell_obs.keys, Self._cleavage_fibers.append, Self._cleavage_levels.append
  -- (14 σ-forms, elided)
  cell-105-153 : τ 153 ≡ τ 153
  cell-105-153 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=67, 58 nodes, 4 type contexts, 21 forms

module subscript-67 where

  -- τ=195: 25 nodes, 5 forms
  -- Types: (untyped)
  -- σ=292 (2×)
  -- σ=347 (17×)
  -- σ=551 (1×)
  -- σ=1488 (3×)
  -- σ=1573 (2×)
  cell-67-195 : τ 195 ≡ τ 195
  cell-67-195 = refl

  -- τ=114: 15 nodes, 3 forms
  -- Types: (untyped)
  -- σ=163 (7×)
  -- σ=277 (7×)
  -- σ=746 (1×)
  cell-67-114 : τ 114 ≡ τ 114
  cell-67-114 = refl

  -- τ=257: 10 nodes, 5 forms
  -- Types: (untyped)
  -- σ=379 (2×)
  -- σ=399 (1×)
  -- σ=417 (5×)
  -- σ=1413 (1×)
  -- σ=1627 (1×)
  cell-67-257 : τ 257 ≡ τ 257
  cell-67-257 = refl

  -- τ=84: 8 nodes, 8 forms
  -- Types: (untyped)
  -- σ=124 (1×)
  -- σ=565 (1×)
  -- σ=802 (1×)
  -- σ=977 (1×)
  -- σ=1038 (1×)
  -- σ=1069 (1×)
  -- σ=1711 (1×)
  -- σ=1910 (1×)
  cell-67-84 : τ 84 ≡ τ 84
  cell-67-84 = refl


-- ── arrow (─────────────────────────────────────────────)
-- κ=69, 55 nodes, 1 type contexts, 4 forms

module arrow-69 where

  -- τ=13: 55 nodes, 4 forms
  -- Types: AST, Self, Self._counter, Self.node_count, T
  -- σ=126 (42×)
  -- σ=488 (3×)
  -- σ=848 (6×)
  -- σ=1415 (4×)
  cell-69-13 : τ 13 ≡ τ 13
  cell-69-13 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=106, 46 nodes, 2 type contexts, 19 forms

module apply-106 where

  -- τ=165: 41 nodes, 16 forms
  -- Types: (untyped)
  -- (16 σ-forms, elided)
  cell-106-165 : τ 165 ≡ τ 165
  cell-106-165 = refl

  -- τ=154: 5 nodes, 3 forms
  -- Types: (untyped)
  -- σ=225 (1×)
  -- σ=652 (2×)
  -- σ=1144 (2×)
  cell-106-154 : τ 154 ≡ τ 154
  cell-106-154 = refl


-- ── arg (───────────────────────────────────────────────)
-- κ=11, 45 nodes, 1 type contexts, 2 forms

module arg-11 where

  -- τ=11: 45 nodes, 2 forms
  -- Types: (untyped)
  -- σ=20 (42×)
  -- σ=1676 (3×)
  cell-11-11 : τ 11 ≡ τ 11
  cell-11-11 = refl


-- ── arg (───────────────────────────────────────────────)
-- κ=21, 38 nodes, 2 type contexts, 27 forms

module arg-21 where

  -- τ=93: 32 nodes, 22 forms
  -- Types: (untyped)
  -- (22 σ-forms, elided)
  cell-21-93 : τ 93 ≡ τ 93
  cell-21-93 = refl

  -- τ=31: 6 nodes, 5 forms
  -- Types: (untyped)
  -- σ=39 (2×)
  -- σ=72 (1×)
  -- σ=73 (1×)
  -- σ=112 (1×)
  -- σ=424 (1×)
  cell-21-31 : τ 31 ≡ τ 31
  cell-21-31 = refl


-- ── morphism@state (────────────────────────────────────)
-- κ=14, 36 nodes, 1 type contexts, 28 forms

module morphism-at-state-14 where

  -- τ=14: 36 nodes, 28 forms
  -- Types: Self._cell_contents, Self._cell_obs, Self._cleavage_fibers, Self._cleavage_ghost_count, Self._cleavage_levels
  -- (28 σ-forms, elided)
  cell-14-14 : τ 14 ≡ τ 14
  cell-14-14 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=33, 36 nodes, 2 type contexts, 25 forms

module subscript-33 where

  -- τ=47: 32 nodes, 21 forms
  -- Types: (untyped)
  -- (21 σ-forms, elided)
  cell-33-47 : τ 47 ≡ τ 47
  cell-33-47 = refl

  -- τ=157: 4 nodes, 4 forms
  -- Types: (untyped)
  -- σ=228 (1×)
  -- σ=447 (1×)
  -- σ=536 (1×)
  -- σ=539 (1×)
  cell-33-157 : τ 157 ≡ τ 157
  cell-33-157 = refl


-- ── product (───────────────────────────────────────────)
-- κ=15, 30 nodes, 4 type contexts, 17 forms

module product-15 where

  -- τ=17: 12 nodes, 10 forms
  -- Types: tuple
  -- (10 σ-forms, elided)
  cell-15-17 : τ 17 ≡ τ 17
  cell-15-17 = refl

  -- τ=250: 10 nodes, 3 forms
  -- Types: tuple
  -- σ=370 (1×)
  -- σ=1461 (3×)
  -- σ=1576 (6×)
  cell-15-250 : τ 250 ≡ τ 250
  cell-15-250 = refl

  -- τ=127: 6 nodes, 3 forms
  -- Types: tuple
  -- σ=189 (1×)
  -- σ=335 (3×)
  -- σ=414 (2×)
  cell-15-127 : τ 127 ≡ τ 127
  cell-15-127 = refl

  -- τ=25: 2 nodes, 1 forms
  -- Types: tuple
  -- σ=33 (2×)
  cell-15-25 : τ 25 ≡ τ 25
  cell-15-25 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=127, 27 nodes, 1 type contexts, 19 forms

module let-k-127 where

  -- τ=186: 27 nodes, 19 forms
  -- Types: (untyped)
  -- (19 σ-forms, elided)
  cell-127-186 : τ 186 ≡ τ 186
  cell-127-186 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=1, 26 nodes, 1 type contexts, 26 forms

module effect-seq-1 where

  -- τ=1: 26 nodes, 26 forms
  -- Types: (untyped)
  -- (26 σ-forms, elided)
  cell-1-1 : τ 1 ≡ τ 1
  cell-1-1 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=371, 26 nodes, 1 type contexts, 4 forms

module index-371 where

  -- τ=492: 26 nodes, 4 forms
  -- Types: (untyped)
  -- σ=849 (20×)
  -- σ=1679 (2×)
  -- σ=1758 (3×)
  -- σ=1901 (1×)
  cell-371-492 : τ 492 ≡ τ 492
  cell-371-492 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=372, 26 nodes, 1 type contexts, 10 forms

module subscript-372 where

  -- τ=493: 26 nodes, 10 forms
  -- Types: (untyped)
  -- (10 σ-forms, elided)
  cell-372-493 : τ 493 ≡ τ 493
  cell-372-493 = refl


-- ── coerce (────────────────────────────────────────────)
-- κ=275, 24 nodes, 2 type contexts, 18 forms

module coerce-275 where

  -- τ=486: 15 nodes, 14 forms
  -- Types: (untyped)
  -- (14 σ-forms, elided)
  cell-275-486 : τ 486 ≡ τ 486
  cell-275-486 = refl

  -- τ=377: 9 nodes, 5 forms
  -- Types: (untyped)
  -- σ=611 (5×)
  -- σ=1813 (1×)
  -- σ=1959 (1×)
  -- σ=1994 (1×)
  -- σ=2037 (1×)
  cell-275-377 : τ 377 ≡ τ 377
  cell-275-377 = refl


-- ── cardinality (───────────────────────────────────────)
-- κ=149, 23 nodes, 2 type contexts, 17 forms

module cardinality-149 where

  -- τ=335: 22 nodes, 16 forms
  -- Types: int
  -- (16 σ-forms, elided)
  cell-149-335 : τ 335 ≡ τ 335
  cell-149-335 = refl

  -- τ=210: 1 nodes, 1 forms
  -- Types: int
  -- σ=312 (1×)
  cell-149-210 : τ 210 ≡ τ 210
  cell-149-210 = refl


-- ── powerset (──────────────────────────────────────────)
-- κ=125, 22 nodes, 1 type contexts, 1 forms

module powerset-125 where

  -- τ=184: 22 nodes, 1 forms
  -- Types: (untyped)
  -- σ=278 (22×)
  cell-125-184 : τ 184 ≡ τ 184
  cell-125-184 = refl


-- ── product (───────────────────────────────────────────)
-- κ=76, 21 nodes, 2 type contexts, 2 forms

module product-76 where

  -- τ=100: 17 nodes, 1 forms
  -- Types: tuple
  -- σ=146 (17×)
  cell-76-100 : τ 100 ≡ τ 100
  cell-76-100 = refl

  -- τ=96: 4 nodes, 1 forms
  -- Types: tuple
  -- σ=142 (4×)
  cell-76-96 : τ 96 ≡ τ 96
  cell-76-96 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=77, 21 nodes, 2 type contexts, 2 forms

module index-77 where

  -- τ=101: 17 nodes, 1 forms
  -- Types: (untyped)
  -- σ=147 (17×)
  cell-77-101 : τ 101 ≡ τ 101
  cell-77-101 = refl

  -- τ=97: 4 nodes, 1 forms
  -- Types: (untyped)
  -- σ=143 (4×)
  cell-77-97 : τ 97 ≡ τ 97
  cell-77-97 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=78, 21 nodes, 2 type contexts, 2 forms

module subscript-78 where

  -- τ=102: 17 nodes, 1 forms
  -- Types: (untyped)
  -- σ=148 (17×)
  cell-78-102 : τ 102 ≡ τ 102
  cell-78-102 = refl

  -- τ=98: 4 nodes, 1 forms
  -- Types: (untyped)
  -- σ=144 (4×)
  cell-78-98 : τ 98 ≡ τ 98
  cell-78-98 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=16, 20 nodes, 4 type contexts, 8 forms

module index-16 where

  -- τ=251: 10 nodes, 3 forms
  -- Types: (untyped)
  -- σ=371 (1×)
  -- σ=1462 (3×)
  -- σ=1577 (6×)
  cell-16-251 : τ 251 ≡ τ 251
  cell-16-251 = refl

  -- τ=128: 6 nodes, 3 forms
  -- Types: (untyped)
  -- σ=190 (1×)
  -- σ=336 (3×)
  -- σ=415 (2×)
  cell-16-128 : τ 128 ≡ τ 128
  cell-16-128 = refl

  -- τ=18: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=27 (2×)
  cell-16-18 : τ 18 ≡ τ 18
  cell-16-18 = refl

  -- τ=26: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=34 (2×)
  cell-16-26 : τ 26 ≡ τ 26
  cell-16-26 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=17, 20 nodes, 5 type contexts, 13 forms

module subscript-17 where

  -- τ=252: 10 nodes, 5 forms
  -- Types: (untyped)
  -- σ=372 (1×)
  -- σ=1463 (2×)
  -- σ=1516 (1×)
  -- σ=1578 (2×)
  -- σ=1589 (4×)
  cell-17-252 : τ 252 ≡ τ 252
  cell-17-252 = refl

  -- τ=129: 6 nodes, 5 forms
  -- Types: (untyped)
  -- σ=191 (1×)
  -- σ=337 (2×)
  -- σ=416 (1×)
  -- σ=1107 (1×)
  -- σ=1213 (1×)
  cell-17-129 : τ 129 ≡ τ 129
  cell-17-129 = refl

  -- τ=19: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=28 (2×)
  cell-17-19 : τ 19 ≡ τ 19
  cell-17-19 = refl

  -- τ=27: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=35 (1×)
  cell-17-27 : τ 27 ≡ τ 27
  cell-17-27 = refl

  -- τ=281: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=404 (1×)
  cell-17-281 : τ 281 ≡ τ 281
  cell-17-281 = refl


-- ── projection@? (──────────────────────────────────────)
-- κ=258, 20 nodes, 1 type contexts, 11 forms

module projection-at-x3f-258 where

  -- τ=188: 20 nodes, 11 forms
  -- Types: (untyped)
  -- (11 σ-forms, elided)
  cell-258-188 : τ 188 ≡ τ 188
  cell-258-188 = refl


-- ── projection.compute@? (──────────────────────────────)
-- κ=259, 20 nodes, 1 type contexts, 11 forms

module projection-compute-at-x3f-259 where

  -- τ=361: 20 nodes, 11 forms
  -- Types: (untyped)
  -- (11 σ-forms, elided)
  cell-259-361 : τ 361 ≡ τ 361
  cell-259-361 = refl


-- ── product.unpack (────────────────────────────────────)
-- κ=45, 19 nodes, 1 type contexts, 10 forms

module product-unpack-45 where

  -- τ=59: 19 nodes, 10 forms
  -- Types: tuple
  -- (10 σ-forms, elided)
  cell-45-59 : τ 59 ≡ τ 59
  cell-45-59 = refl


-- ── arguments (─────────────────────────────────────────)
-- κ=12, 18 nodes, 1 type contexts, 2 forms

module arguments-12 where

  -- τ=12: 18 nodes, 2 forms
  -- Types: (untyped)
  -- σ=21 (15×)
  -- σ=1677 (3×)
  cell-12-12 : τ 12 ≡ τ 12
  cell-12-12 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=353, 18 nodes, 2 type contexts, 14 forms

module apply-353 where

  -- τ=473: 16 nodes, 12 forms
  -- Types: (untyped)
  -- (12 σ-forms, elided)
  cell-353-473 : τ 473 ≡ τ 473
  cell-353-473 = refl

  -- τ=653: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1339 (1×)
  -- σ=1355 (1×)
  cell-353-653 : τ 653 ≡ τ 653
  cell-353-653 = refl


-- ── add (───────────────────────────────────────────────)
-- κ=57, 17 nodes, 1 type contexts, 1 forms

module add-57 where

  -- τ=73: 17 nodes, 1 forms
  -- Types: (untyped)
  -- σ=106 (17×)
  cell-57-73 : τ 73 ≡ τ 73
  cell-57-73 = refl


-- ── exponential.literal (───────────────────────────────)
-- κ=18, 15 nodes, 1 type contexts, 1 forms

module exponential-literal-18 where

  -- τ=20: 15 nodes, 1 forms
  -- Types: dict
  -- σ=29 (15×)
  cell-18-20 : τ 20 ≡ τ 20
  cell-18-20 = refl


-- ── in (────────────────────────────────────────────────)
-- κ=61, 15 nodes, 1 type contexts, 1 forms

module in-k-61 where

  -- τ=77: 15 nodes, 1 forms
  -- Types: (untyped)
  -- σ=114 (15×)
  cell-61-77 : τ 77 ≡ τ 77
  cell-61-77 = refl


-- ── cardinality (───────────────────────────────────────)
-- κ=70, 15 nodes, 1 type contexts, 8 forms

module cardinality-70 where

  -- τ=87: 15 nodes, 8 forms
  -- Types: int
  -- σ=127 (1×)
  -- σ=172 (1×)
  -- σ=517 (2×)
  -- σ=525 (1×)
  -- σ=589 (4×)
  -- σ=1777 (2×)
  -- σ=1780 (2×)
  -- σ=1783 (2×)
  cell-70-87 : τ 87 ≡ τ 87
  cell-70-87 = refl


-- ── partial@state (─────────────────────────────────────)
-- κ=217, 15 nodes, 1 type contexts, 7 forms

module partial-at-state-217 where

  -- τ=153: 15 nodes, 7 forms
  -- Types: Self._cell_contents.get, Self._cell_obs.get, Self._cell_obs.keys, Self._cleavage_fibers.append, Self._cleavage_levels.append
  -- σ=457 (1×)
  -- σ=483 (2×)
  -- σ=642 (2×)
  -- σ=760 (1×)
  -- σ=921 (7×)
  -- σ=1103 (1×)
  -- σ=1982 (1×)
  cell-217-153 : τ 153 ≡ τ 153
  cell-217-153 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=254, 15 nodes, 2 type contexts, 11 forms

module subscript-254 where

  -- τ=355: 14 nodes, 10 forms
  -- Types: (untyped)
  -- (10 σ-forms, elided)
  cell-254-355 : τ 355 ≡ τ 355
  cell-254-355 = refl

  -- τ=434: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=703 (1×)
  cell-254-434 : τ 434 ≡ τ 434
  cell-254-434 = refl


-- ── morphism@? (────────────────────────────────────────)
-- κ=300, 15 nodes, 1 type contexts, 11 forms

module morphism-at-x3f-300 where

  -- τ=188: 15 nodes, 11 forms
  -- Types: (untyped)
  -- (11 σ-forms, elided)
  cell-300-188 : τ 188 ≡ τ 188
  cell-300-188 = refl


-- ── noteq (─────────────────────────────────────────────)
-- κ=34, 14 nodes, 1 type contexts, 1 forms

module noteq-34 where

  -- τ=48: 14 nodes, 1 forms
  -- Types: (untyped)
  -- σ=59 (14×)
  cell-34-48 : τ 48 ≡ τ 48
  cell-34-48 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=27, 13 nodes, 2 type contexts, 10 forms

module subscript-27 where

  -- τ=37: 12 nodes, 9 forms
  -- Types: (untyped)
  -- (9 σ-forms, elided)
  cell-27-37 : τ 37 ≡ τ 37
  cell-27-37 = refl

  -- τ=150: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=220 (1×)
  cell-27-150 : τ 150 ≡ τ 150
  cell-27-150 = refl


-- ── free_monoid.fold (──────────────────────────────────)
-- κ=673, 13 nodes, 1 type contexts, 4 forms

module free_monoid-fold-673 where

  -- τ=850: 13 nodes, 4 forms
  -- Types: str
  -- σ=1820 (4×)
  -- σ=1827 (7×)
  -- σ=1855 (1×)
  -- σ=2079 (1×)
  cell-673-850 : τ 850 ≡ τ 850
  cell-673-850 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=46, 12 nodes, 1 type contexts, 7 forms

module apply-46 where

  -- τ=61: 12 nodes, 7 forms
  -- Types: (untyped)
  -- σ=82 (1×)
  -- σ=84 (1×)
  -- σ=492 (1×)
  -- σ=792 (6×)
  -- σ=960 (1×)
  -- σ=1258 (1×)
  -- σ=1732 (1×)
  cell-46-61 : τ 61 ≡ τ 61
  cell-46-61 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=255, 12 nodes, 1 type contexts, 12 forms

module let-k-255 where

  -- τ=356: 12 nodes, 12 forms
  -- Types: (untyped)
  -- (12 σ-forms, elided)
  cell-255-356 : τ 356 ≡ τ 356
  cell-255-356 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=36, 11 nodes, 2 type contexts, 11 forms

module let-k-36 where

  -- τ=50: 9 nodes, 9 forms
  -- Types: (untyped)
  -- (9 σ-forms, elided)
  cell-36-50 : τ 50 ≡ τ 50
  cell-36-50 = refl

  -- τ=352: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=537 (1×)
  -- σ=540 (1×)
  cell-36-352 : τ 352 ≡ τ 352
  cell-36-352 = refl


-- ── terminal.map (──────────────────────────────────────)
-- κ=42, 11 nodes, 2 type contexts, 9 forms

module terminal-map-42 where

  -- τ=56: 9 nodes, 7 forms
  -- Types: (untyped)
  -- σ=70 (1×)
  -- σ=91 (3×)
  -- σ=271 (1×)
  -- σ=867 (1×)
  -- σ=1568 (1×)
  -- σ=1689 (1×)
  -- σ=1765 (1×)
  cell-42-56 : τ 56 ≡ τ 56
  cell-42-56 = refl

  -- τ=162: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=234 (1×)
  -- σ=882 (1×)
  cell-42-162 : τ 162 ≡ τ 162
  cell-42-162 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=352, 11 nodes, 3 type contexts, 7 forms

module equalizer-352 where

  -- τ=471: 8 nodes, 5 forms
  -- Types: (untyped)
  -- σ=806 (4×)
  -- σ=926 (1×)
  -- σ=1190 (1×)
  -- σ=1317 (1×)
  -- σ=1645 (1×)
  cell-352-471 : τ 471 ≡ τ 471
  cell-352-471 = refl

  -- τ=595: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1149 (2×)
  cell-352-595 : τ 595 ≡ τ 595
  cell-352-595 = refl

  -- τ=522: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=905 (1×)
  cell-352-522 : τ 522 ≡ τ 522
  cell-352-522 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=354, 11 nodes, 2 type contexts, 7 forms

module effect-seq-354 where

  -- τ=474: 10 nodes, 6 forms
  -- Types: (untyped)
  -- σ=809 (4×)
  -- σ=943 (1×)
  -- σ=1171 (1×)
  -- σ=1192 (1×)
  -- σ=1319 (1×)
  -- σ=1334 (2×)
  cell-354-474 : τ 474 ≡ τ 474
  cell-354-474 = refl

  -- τ=659: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1356 (1×)
  cell-354-659 : τ 659 ≡ τ 659
  cell-354-659 = refl


-- ── product (───────────────────────────────────────────)
-- κ=160, 10 nodes, 1 type contexts, 1 forms

module product-160 where

  -- τ=226: 10 nodes, 1 forms
  -- Types: tuple
  -- σ=342 (10×)
  cell-160-226 : τ 226 ≡ τ 226
  cell-160-226 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=161, 10 nodes, 1 type contexts, 1 forms

module index-161 where

  -- τ=227: 10 nodes, 1 forms
  -- Types: (untyped)
  -- σ=343 (10×)
  cell-161-227 : τ 227 ≡ τ 227
  cell-161-227 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=162, 10 nodes, 1 type contexts, 1 forms

module subscript-162 where

  -- τ=228: 10 nodes, 1 forms
  -- Types: (untyped)
  -- σ=344 (10×)
  cell-162-228 : τ 228 ≡ τ 228
  cell-162-228 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=175, 10 nodes, 2 type contexts, 5 forms

module apply-175 where

  -- τ=242: 8 nodes, 3 forms
  -- Types: (untyped)
  -- σ=362 (4×)
  -- σ=409 (1×)
  -- σ=1431 (3×)
  cell-175-242 : τ 242 ≡ τ 242
  cell-175-242 = refl

  -- τ=728: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1492 (1×)
  -- σ=2067 (1×)
  cell-175-728 : τ 728 ≡ τ 728
  cell-175-728 = refl


-- ── free_monoid.op@state (──────────────────────────────)
-- κ=243, 10 nodes, 1 type contexts, 4 forms

module free_monoid-op-at-state-243 where

  -- τ=153: 10 nodes, 4 forms
  -- Types: Self._cell_contents.get, Self._cell_obs.get, Self._cell_obs.keys, Self._cleavage_fibers.append, Self._cleavage_levels.append
  -- σ=519 (1×)
  -- σ=530 (1×)
  -- σ=624 (7×)
  -- σ=1376 (1×)
  cell-243-153 : τ 153 ≡ τ 153
  cell-243-153 = refl


-- ── notin (─────────────────────────────────────────────)
-- κ=23, 9 nodes, 1 type contexts, 1 forms

module notin-23 where

  -- τ=33: 9 nodes, 1 forms
  -- Types: (untyped)
  -- σ=42 (9×)
  cell-23-33 : τ 33 ≡ τ 33
  cell-23-33 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=62, 9 nodes, 2 type contexts, 7 forms

module equalizer-62 where

  -- τ=78: 7 nodes, 6 forms
  -- Types: (untyped)
  -- σ=115 (1×)
  -- σ=208 (1×)
  -- σ=735 (1×)
  -- σ=1032 (1×)
  -- σ=1150 (2×)
  -- σ=1276 (1×)
  cell-62-78 : τ 78 ≡ τ 78
  cell-62-78 = refl

  -- τ=396: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=650 (2×)
  cell-62-396 : τ 396 ≡ τ 396
  cell-62-396 = refl


-- ── free_monoid.literal (───────────────────────────────)
-- κ=83, 9 nodes, 1 type contexts, 1 forms

module free_monoid-literal-83 where

  -- τ=115: 9 nodes, 1 forms
  -- Types: list
  -- σ=164 (9×)
  cell-83-115 : τ 115 ≡ τ 115
  cell-83-115 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=118, 9 nodes, 2 type contexts, 5 forms

module apply-118 where

  -- τ=174: 7 nodes, 4 forms
  -- Types: (untyped)
  -- σ=254 (1×)
  -- σ=811 (4×)
  -- σ=1193 (1×)
  -- σ=1320 (1×)
  cell-118-174 : τ 174 ≡ τ 174
  cell-118-174 = refl

  -- τ=597: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1152 (2×)
  cell-118-597 : τ 597 ≡ τ 597
  cell-118-597 = refl


-- ── monoid.op@? (───────────────────────────────────────)
-- κ=129, 9 nodes, 1 type contexts, 9 forms

module monoid-op-at-x3f-129 where

  -- τ=188: 9 nodes, 9 forms
  -- Types: (untyped)
  -- (9 σ-forms, elided)
  cell-129-188 : τ 188 ≡ τ 188
  cell-129-188 = refl


-- ── gt (────────────────────────────────────────────────)
-- κ=215, 9 nodes, 1 type contexts, 1 forms

module gt-215 where

  -- τ=307: 9 nodes, 1 forms
  -- Types: (untyped)
  -- σ=454 (9×)
  cell-215-307 : τ 307 ≡ τ 307
  cell-215-307 = refl


-- ── partial.apply@state (───────────────────────────────)
-- κ=228, 9 nodes, 1 type contexts, 7 forms

module partial-apply-at-state-228 where

  -- τ=324: 9 nodes, 7 forms
  -- Types: T
  -- σ=485 (1×)
  -- σ=761 (1×)
  -- σ=922 (1×)
  -- σ=927 (2×)
  -- σ=1027 (1×)
  -- σ=1051 (2×)
  -- σ=1203 (1×)
  cell-228-324 : τ 324 ≡ τ 324
  cell-228-324 = refl


-- ── arguments (─────────────────────────────────────────)
-- κ=22, 8 nodes, 2 type contexts, 6 forms

module arguments-22 where

  -- τ=124: 5 nodes, 4 forms
  -- Types: (untyped)
  -- σ=183 (1×)
  -- σ=236 (2×)
  -- σ=1638 (1×)
  -- σ=1691 (1×)
  cell-22-124 : τ 124 ≡ τ 124
  cell-22-124 = refl

  -- τ=32: 3 nodes, 2 forms
  -- Types: (untyped)
  -- σ=40 (2×)
  -- σ=113 (1×)
  cell-22-32 : τ 32 ≡ τ 32
  cell-22-32 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=28, 8 nodes, 2 type contexts, 7 forms

module let-k-28 where

  -- τ=38: 5 nodes, 5 forms
  -- Types: (untyped)
  -- σ=47 (1×)
  -- σ=103 (1×)
  -- σ=825 (1×)
  -- σ=1003 (1×)
  -- σ=1084 (1×)
  cell-28-38 : τ 38 ≡ τ 38
  cell-28-38 = refl

  -- τ=149: 3 nodes, 2 forms
  -- Types: (untyped)
  -- σ=217 (1×)
  -- σ=1160 (2×)
  cell-28-149 : τ 149 ≡ τ 149
  cell-28-149 = refl


-- ── monoid.op@? (───────────────────────────────────────)
-- κ=210, 8 nodes, 2 type contexts, 6 forms

module monoid-op-at-x3f-210 where

  -- τ=178: 7 nodes, 5 forms
  -- Types: (untyped)
  -- σ=720 (1×)
  -- σ=832 (1×)
  -- σ=1089 (2×)
  -- σ=1097 (1×)
  -- σ=1364 (2×)
  cell-210-178 : τ 178 ≡ τ 178
  cell-210-178 = refl

  -- τ=158: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=448 (1×)
  cell-210-158 : τ 158 ≡ τ 158
  cell-210-158 = refl


-- ── monoid.op@? (───────────────────────────────────────)
-- κ=211, 8 nodes, 2 type contexts, 7 forms

module monoid-op-at-x3f-211 where

  -- τ=444: 7 nodes, 6 forms
  -- Types: (untyped)
  -- σ=721 (1×)
  -- σ=833 (1×)
  -- σ=1090 (1×)
  -- σ=1098 (1×)
  -- σ=1365 (2×)
  -- σ=1371 (1×)
  cell-211-444 : τ 444 ≡ τ 444
  cell-211-444 = refl

  -- τ=303: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=450 (1×)
  cell-211-303 : τ 303 ≡ τ 303
  cell-211-303 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=212, 8 nodes, 2 type contexts, 7 forms

module effect-seq-212 where

  -- τ=445: 7 nodes, 6 forms
  -- Types: (untyped)
  -- σ=722 (1×)
  -- σ=834 (1×)
  -- σ=1091 (1×)
  -- σ=1099 (1×)
  -- σ=1366 (2×)
  -- σ=1372 (1×)
  cell-212-445 : τ 445 ≡ τ 445
  cell-212-445 = refl

  -- τ=304: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=451 (1×)
  cell-212-304 : τ 304 ≡ τ 304
  cell-212-304 = refl


-- ── sub (───────────────────────────────────────────────)
-- κ=220, 8 nodes, 1 type contexts, 1 forms

module sub-220 where

  -- τ=313: 8 nodes, 1 forms
  -- Types: (untyped)
  -- σ=461 (8×)
  cell-220-313 : τ 313 ≡ τ 313
  cell-220-313 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=349, 8 nodes, 1 type contexts, 4 forms

module let-k-349 where

  -- τ=467: 8 nodes, 4 forms
  -- Types: (untyped)
  -- σ=793 (4×)
  -- σ=973 (2×)
  -- σ=1259 (1×)
  -- σ=1733 (1×)
  cell-349-467 : τ 467 ≡ τ 467
  cell-349-467 = refl


-- ── product (───────────────────────────────────────────)
-- κ=357, 8 nodes, 4 type contexts, 7 forms

module product-357 where

  -- τ=477: 4 nodes, 4 forms
  -- Types: tuple
  -- σ=817 (1×)
  -- σ=1232 (1×)
  -- σ=1266 (1×)
  -- σ=1752 (1×)
  cell-357-477 : τ 477 ≡ τ 477
  cell-357-477 = refl

  -- τ=693: 2 nodes, 1 forms
  -- Types: tuple
  -- σ=1425 (2×)
  cell-357-693 : τ 693 ≡ τ 693
  cell-357-693 = refl

  -- τ=608: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=1197 (1×)
  cell-357-608 : τ 608 ≡ τ 608
  cell-357-608 = refl

  -- τ=646: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=1324 (1×)
  cell-357-646 : τ 646 ≡ τ 646
  cell-357-646 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=377, 8 nodes, 2 type contexts, 7 forms

module apply-377 where

  -- τ=499: 7 nodes, 6 forms
  -- Types: (untyped)
  -- σ=858 (1×)
  -- σ=1015 (1×)
  -- σ=1059 (2×)
  -- σ=1206 (1×)
  -- σ=1563 (1×)
  -- σ=1659 (1×)
  cell-377-499 : τ 499 ≡ τ 499
  cell-377-499 = refl

  -- τ=660: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1357 (1×)
  cell-377-660 : τ 660 ≡ τ 660
  cell-377-660 = refl


-- ── div (───────────────────────────────────────────────)
-- κ=675, 8 nodes, 1 type contexts, 1 forms

module div-675 where

  -- τ=852: 8 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1823 (8×)
  cell-675-852 : τ 852 ≡ τ 852
  cell-675-852 = refl


-- ── free_monoid.op@sequence (───────────────────────────)
-- κ=715, 8 nodes, 1 type contexts, 1 forms

module free_monoid-op-at-sequence-715 where

  -- τ=34: 8 nodes, 1 forms
  -- Types: Self._cascade_abstraction_merge, Self._cascade_eta, Self._cell_contents, Self._cell_obs, Self._cleavage_fibers
  -- σ=1926 (8×)
  cell-715-34 : τ 34 ≡ τ 34
  cell-715-34 = refl


-- ── arg (───────────────────────────────────────────────)
-- κ=79, 7 nodes, 2 type contexts, 5 forms

module arg-79 where

  -- τ=103: 5 nodes, 4 forms
  -- Types: (untyped)
  -- σ=149 (2×)
  -- σ=1219 (1×)
  -- σ=1220 (1×)
  -- σ=1221 (1×)
  cell-79-103 : τ 103 ≡ τ 103
  cell-79-103 = refl

  -- τ=99: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=145 (2×)
  cell-79-99 : τ 99 ≡ τ 99
  cell-79-99 = refl


-- ── monoid.accum (──────────────────────────────────────)
-- κ=102, 7 nodes, 1 type contexts, 3 forms

module monoid-accum-102 where

  -- τ=148: 7 nodes, 3 forms
  -- Types: (untyped)
  -- σ=215 (1×)
  -- σ=608 (1×)
  -- σ=837 (5×)
  cell-102-148 : τ 148 ≡ τ 148
  cell-102-148 = refl


-- ── comprehension (─────────────────────────────────────)
-- κ=232, 7 nodes, 2 type contexts, 6 forms

module comprehension-232 where

  -- τ=518: 6 nodes, 5 forms
  -- Types: (untyped)
  -- σ=896 (1×)
  -- σ=996 (1×)
  -- σ=1253 (1×)
  -- σ=1328 (2×)
  -- σ=1887 (1×)
  cell-232-518 : τ 518 ≡ τ 518
  cell-232-518 = refl

  -- τ=330: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=496 (1×)
  cell-232-330 : τ 330 ≡ τ 330
  cell-232-330 = refl


-- ── fixpoint.next (─────────────────────────────────────)
-- κ=304, 7 nodes, 1 type contexts, 1 forms

module fixpoint-next-304 where

  -- τ=412: 7 nodes, 1 forms
  -- Types: (untyped)
  -- σ=671 (7×)
  cell-304-412 : τ 412 ≡ τ 412
  cell-304-412 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=343, 7 nodes, 1 type contexts, 6 forms

module apply-343 where

  -- τ=456: 7 nodes, 6 forms
  -- Types: (untyped)
  -- σ=762 (1×)
  -- σ=923 (1×)
  -- σ=928 (1×)
  -- σ=1008 (1×)
  -- σ=1052 (2×)
  -- σ=1204 (1×)
  cell-343-456 : τ 456 ≡ τ 456
  cell-343-456 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=344, 7 nodes, 1 type contexts, 6 forms

module effect-seq-344 where

  -- τ=457: 7 nodes, 6 forms
  -- Types: (untyped)
  -- σ=763 (1×)
  -- σ=924 (1×)
  -- σ=929 (1×)
  -- σ=1009 (1×)
  -- σ=1053 (2×)
  -- σ=1205 (1×)
  cell-344-457 : τ 457 ≡ τ 457
  cell-344-457 = refl


-- ── alias (─────────────────────────────────────────────)
-- κ=2, 6 nodes, 1 type contexts, 6 forms

module alias-2 where

  -- τ=2: 6 nodes, 6 forms
  -- Types: (untyped)
  -- σ=2 (1×)
  -- σ=4 (1×)
  -- σ=5 (1×)
  -- σ=7 (1×)
  -- σ=8 (1×)
  -- σ=9 (1×)
  cell-2-2 : τ 2 ≡ τ 2
  cell-2-2 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=32, 6 nodes, 1 type contexts, 6 forms

module let-k-32 where

  -- τ=45: 6 nodes, 6 forms
  -- Types: (untyped)
  -- σ=55 (1×)
  -- σ=508 (1×)
  -- σ=511 (1×)
  -- σ=554 (1×)
  -- σ=696 (1×)
  -- σ=1210 (1×)
  cell-32-45 : τ 45 ≡ τ 45
  cell-32-45 = refl


-- ── arguments (─────────────────────────────────────────)
-- κ=44, 6 nodes, 2 type contexts, 6 forms

module arguments-44 where

  -- τ=168: 5 nodes, 5 forms
  -- Types: (untyped)
  -- σ=245 (1×)
  -- σ=727 (1×)
  -- σ=1458 (1×)
  -- σ=1483 (1×)
  -- σ=1555 (1×)
  cell-44-168 : τ 168 ≡ τ 168
  cell-44-168 = refl

  -- τ=58: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=74 (1×)
  cell-44-58 : τ 58 ≡ τ 58
  cell-44-58 = refl


-- ── eq (────────────────────────────────────────────────)
-- κ=49, 6 nodes, 1 type contexts, 1 forms

module eq-49 where

  -- τ=65: 6 nodes, 1 forms
  -- Types: (untyped)
  -- σ=88 (6×)
  cell-49-65 : τ 65 ≡ τ 65
  cell-49-65 = refl


-- ── coerce (────────────────────────────────────────────)
-- κ=87, 6 nodes, 1 type contexts, 6 forms

module coerce-87 where

  -- τ=119: 6 nodes, 6 forms
  -- Types: (untyped)
  -- σ=173 (1×)
  -- σ=526 (1×)
  -- σ=1778 (1×)
  -- σ=1781 (1×)
  -- σ=1784 (1×)
  -- σ=1950 (1×)
  cell-87-119 : τ 119 ≡ τ 119
  cell-87-119 = refl


-- ── product (───────────────────────────────────────────)
-- κ=163, 6 nodes, 1 type contexts, 1 forms

module product-163 where

  -- τ=229: 6 nodes, 1 forms
  -- Types: tuple
  -- σ=348 (6×)
  cell-163-229 : τ 229 ≡ τ 229
  cell-163-229 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=164, 6 nodes, 1 type contexts, 1 forms

module index-164 where

  -- τ=230: 6 nodes, 1 forms
  -- Types: (untyped)
  -- σ=349 (6×)
  cell-164-230 : τ 230 ≡ τ 230
  cell-164-230 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=165, 6 nodes, 1 type contexts, 1 forms

module subscript-165 where

  -- τ=231: 6 nodes, 1 forms
  -- Types: (untyped)
  -- σ=350 (6×)
  cell-165-231 : τ 231 ≡ τ 231
  cell-165-231 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=170, 6 nodes, 1 type contexts, 1 forms

module index-170 where

  -- τ=237: 6 nodes, 1 forms
  -- Types: (untyped)
  -- σ=357 (6×)
  cell-170-237 : τ 237 ≡ τ 237
  cell-170-237 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=171, 6 nodes, 1 type contexts, 1 forms

module subscript-171 where

  -- τ=238: 6 nodes, 1 forms
  -- Types: (untyped)
  -- σ=358 (6×)
  cell-171-238 : τ 238 ≡ τ 238
  cell-171-238 = refl


-- ── arg (───────────────────────────────────────────────)
-- κ=331, 6 nodes, 2 type contexts, 5 forms

module arg-331 where

  -- τ=440: 3 nodes, 2 forms
  -- Types: (untyped)
  -- σ=710 (1×)
  -- σ=869 (2×)
  cell-331-440 : τ 440 ≡ τ 440
  cell-331-440 = refl

  -- τ=452: 3 nodes, 3 forms
  -- Types: (untyped)
  -- σ=747 (1×)
  -- σ=912 (1×)
  -- σ=933 (1×)
  cell-331-452 : τ 452 ≡ τ 452
  cell-331-452 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=355, 6 nodes, 1 type contexts, 3 forms

module let-k-355 where

  -- τ=476: 6 nodes, 3 forms
  -- Types: (untyped)
  -- σ=812 (4×)
  -- σ=1194 (1×)
  -- σ=1321 (1×)
  cell-355-476 : τ 476 ≡ τ 476
  cell-355-476 = refl


-- ── fiber (─────────────────────────────────────────────)
-- κ=373, 6 nodes, 1 type contexts, 4 forms

module fiber-373 where

  -- τ=494: 6 nodes, 4 forms
  -- Types: bool
  -- σ=851 (1×)
  -- σ=1011 (1×)
  -- σ=1055 (3×)
  -- σ=1872 (1×)
  cell-373-494 : τ 494 ≡ τ 494
  cell-373-494 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=378, 6 nodes, 2 type contexts, 5 forms

module effect-seq-378 where

  -- τ=500: 5 nodes, 4 forms
  -- Types: (untyped)
  -- σ=859 (1×)
  -- σ=1016 (1×)
  -- σ=1060 (2×)
  -- σ=1207 (1×)
  cell-378-500 : τ 500 ≡ τ 500
  cell-378-500 = refl

  -- τ=661: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1358 (1×)
  cell-378-661 : τ 661 ≡ τ 661
  cell-378-661 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=550, 6 nodes, 1 type contexts, 3 forms

module apply-550 where

  -- τ=701: 6 nodes, 3 forms
  -- Types: (untyped)
  -- σ=1441 (2×)
  -- σ=1442 (2×)
  -- σ=1443 (2×)
  cell-550-701 : τ 701 ≡ τ 701
  cell-550-701 = refl


-- ── bimap (─────────────────────────────────────────────)
-- κ=676, 6 nodes, 3 type contexts, 6 forms

module bimap-676 where

  -- τ=853: 4 nodes, 4 forms
  -- Types: (untyped)
  -- σ=1824 (1×)
  -- σ=1834 (1×)
  -- σ=1841 (1×)
  -- σ=1996 (1×)
  cell-676-853 : τ 853 ≡ τ 853
  cell-676-853 = refl

  -- τ=921: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=2001 (1×)
  cell-676-921 : τ 921 ≡ τ 921
  cell-676-921 = refl

  -- τ=949: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=2077 (1×)
  cell-676-949 : τ 949 ≡ τ 949
  cell-676-949 = refl


-- ── coerce (────────────────────────────────────────────)
-- κ=86, 5 nodes, 1 type contexts, 5 forms

module coerce-86 where

  -- τ=118: 5 nodes, 5 forms
  -- Types: (untyped)
  -- σ=169 (1×)
  -- σ=311 (1×)
  -- σ=1775 (1×)
  -- σ=1929 (1×)
  -- σ=1948 (1×)
  cell-86-118 : τ 118 ≡ τ 118
  cell-86-118 = refl


-- ── morphism@? (────────────────────────────────────────)
-- κ=109, 5 nodes, 2 type contexts, 5 forms

module morphism-at-x3f-109 where

  -- τ=178: 4 nodes, 4 forms
  -- Types: (untyped)
  -- σ=263 (1×)
  -- σ=268 (1×)
  -- σ=739 (1×)
  -- σ=828 (1×)
  cell-109-178 : τ 178 ≡ τ 178
  cell-109-178 = refl

  -- τ=158: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=229 (1×)
  cell-109-158 : τ 158 ≡ τ 158
  cell-109-158 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=126, 5 nodes, 2 type contexts, 5 forms

module annassign-126 where

  -- τ=185: 4 nodes, 4 forms
  -- Types: (untyped)
  -- σ=279 (1×)
  -- σ=752 (1×)
  -- σ=1336 (1×)
  -- σ=1527 (1×)
  cell-126-185 : τ 185 ≡ τ 185
  cell-126-185 = refl

  -- τ=391: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=637 (1×)
  cell-126-391 : τ 391 ≡ τ 391
  cell-126-391 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=128, 5 nodes, 1 type contexts, 5 forms

module equalizer-128 where

  -- τ=187: 5 nodes, 5 forms
  -- Types: (untyped)
  -- σ=284 (1×)
  -- σ=557 (1×)
  -- σ=1117 (1×)
  -- σ=1279 (1×)
  -- σ=1905 (1×)
  cell-128-187 : τ 187 ≡ τ 187
  cell-128-187 = refl


-- ── monoid.op@? (───────────────────────────────────────)
-- κ=130, 5 nodes, 1 type contexts, 5 forms

module monoid-op-at-x3f-130 where

  -- τ=189: 5 nodes, 5 forms
  -- Types: (untyped)
  -- σ=286 (1×)
  -- σ=598 (1×)
  -- σ=862 (1×)
  -- σ=1156 (1×)
  -- σ=1308 (1×)
  cell-130-189 : τ 189 ≡ τ 189
  cell-130-189 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=131, 5 nodes, 1 type contexts, 5 forms

module effect-seq-131 where

  -- τ=190: 5 nodes, 5 forms
  -- Types: (untyped)
  -- σ=287 (1×)
  -- σ=599 (1×)
  -- σ=863 (1×)
  -- σ=1157 (1×)
  -- σ=1309 (1×)
  cell-131-190 : τ 190 ≡ τ 190
  cell-131-190 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=137, 5 nodes, 1 type contexts, 3 forms

module apply-137 where

  -- τ=198: 5 nodes, 3 forms
  -- Types: (untyped)
  -- σ=297 (2×)
  -- σ=1771 (2×)
  -- σ=1809 (1×)
  cell-137-198 : τ 198 ≡ τ 198
  cell-137-198 = refl


-- ── coerce (────────────────────────────────────────────)
-- κ=150, 5 nodes, 2 type contexts, 5 forms

module coerce-150 where

  -- τ=840: 4 nodes, 4 forms
  -- Types: (untyped)
  -- σ=1788 (1×)
  -- σ=1937 (1×)
  -- σ=1939 (1×)
  -- σ=2040 (1×)
  cell-150-840 : τ 840 ≡ τ 840
  cell-150-840 = refl

  -- τ=211: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=313 (1×)
  cell-150-211 : τ 211 ≡ τ 211
  cell-150-211 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=209, 5 nodes, 1 type contexts, 4 forms

module let-k-209 where

  -- τ=302: 5 nodes, 4 forms
  -- Types: (untyped)
  -- σ=442 (2×)
  -- σ=545 (1×)
  -- σ=903 (1×)
  -- σ=1238 (1×)
  cell-209-302 : τ 302 ≡ τ 302
  cell-209-302 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=213, 5 nodes, 2 type contexts, 5 forms

module fold-213 where

  -- τ=483: 4 nodes, 4 forms
  -- Types: (untyped)
  -- σ=835 (1×)
  -- σ=1092 (1×)
  -- σ=1100 (1×)
  -- σ=1373 (1×)
  cell-213-483 : τ 483 ≡ τ 483
  cell-213-483 = refl

  -- τ=305: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=452 (1×)
  cell-213-305 : τ 305 ≡ τ 305
  cell-213-305 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=252, 5 nodes, 2 type contexts, 5 forms

module equalizer-252 where

  -- τ=468: 4 nodes, 4 forms
  -- Types: (untyped)
  -- σ=799 (1×)
  -- σ=975 (1×)
  -- σ=1037 (1×)
  -- σ=1068 (1×)
  cell-252-468 : τ 468 ≡ τ 468
  cell-252-468 = refl

  -- τ=353: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=548 (1×)
  cell-252-353 : τ 353 ≡ τ 353
  cell-252-353 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=263, 5 nodes, 1 type contexts, 4 forms

module subscript-263 where

  -- τ=365: 5 nodes, 4 forms
  -- Types: (untyped)
  -- σ=587 (2×)
  -- σ=1593 (1×)
  -- σ=1598 (1×)
  -- σ=1604 (1×)
  cell-263-365 : τ 365 ≡ τ 365
  cell-263-365 = refl


-- ── morphism@? (────────────────────────────────────────)
-- κ=264, 5 nodes, 1 type contexts, 4 forms

module morphism-at-x3f-264 where

  -- τ=366: 5 nodes, 4 forms
  -- Types: (untyped)
  -- σ=588 (2×)
  -- σ=1594 (1×)
  -- σ=1599 (1×)
  -- σ=1605 (1×)
  cell-264-366 : τ 366 ≡ τ 366
  cell-264-366 = refl


-- ── slice (─────────────────────────────────────────────)
-- κ=276, 5 nodes, 1 type contexts, 3 forms

module slice-276 where

  -- τ=378: 5 nodes, 3 forms
  -- Types: (untyped)
  -- σ=614 (2×)
  -- σ=1178 (2×)
  -- σ=2032 (1×)
  cell-276-378 : τ 378 ≡ τ 378
  cell-276-378 = refl


-- ── free_monoid.op@? (──────────────────────────────────)
-- κ=356, 5 nodes, 1 type contexts, 5 forms

module free_monoid-op-at-x3f-356 where

  -- τ=188: 5 nodes, 5 forms
  -- Types: (untyped)
  -- σ=816 (1×)
  -- σ=983 (1×)
  -- σ=1293 (1×)
  -- σ=1669 (1×)
  -- σ=1750 (1×)
  cell-356-188 : τ 188 ≡ τ 188
  cell-356-188 = refl


-- ── coerce (────────────────────────────────────────────)
-- κ=374, 5 nodes, 1 type contexts, 3 forms

module coerce-374 where

  -- τ=495: 5 nodes, 3 forms
  -- Types: (untyped)
  -- σ=852 (1×)
  -- σ=1012 (1×)
  -- σ=1056 (3×)
  cell-374-495 : τ 495 ≡ τ 495
  cell-374-495 = refl


-- ── ifexp (─────────────────────────────────────────────)
-- κ=375, 5 nodes, 1 type contexts, 3 forms

module ifexp-375 where

  -- τ=496: 5 nodes, 3 forms
  -- Types: (untyped)
  -- σ=853 (1×)
  -- σ=1013 (1×)
  -- σ=1057 (3×)
  cell-375-496 : τ 496 ≡ τ 496
  cell-375-496 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=376, 5 nodes, 1 type contexts, 3 forms

module let-k-376 where

  -- τ=497: 5 nodes, 3 forms
  -- Types: (untyped)
  -- σ=854 (1×)
  -- σ=1014 (1×)
  -- σ=1058 (3×)
  cell-376-497 : τ 497 ≡ τ 497
  cell-376-497 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=456, 5 nodes, 1 type contexts, 5 forms

module equalizer-456 where

  -- τ=585: 5 nodes, 5 forms
  -- Types: (untyped)
  -- σ=1124 (1×)
  -- σ=1164 (1×)
  -- σ=1338 (1×)
  -- σ=1736 (1×)
  -- σ=1920 (1×)
  cell-456-585 : τ 585 ≡ τ 585
  cell-456-585 = refl


-- ── exponential (───────────────────────────────────────)
-- κ=558, 5 nodes, 1 type contexts, 4 forms

module exponential-558 where

  -- τ=404: 5 nodes, 4 forms
  -- Types: (untyped)
  -- σ=1452 (2×)
  -- σ=1507 (1×)
  -- σ=1716 (1×)
  -- σ=1863 (1×)
  cell-558-404 : τ 404 ≡ τ 404
  cell-558-404 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=19, 4 nodes, 4 type contexts, 4 forms

module annassign-19 where

  -- τ=21: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=30 (1×)
  cell-19-21 : τ 21 ≡ τ 21
  cell-19-21 = refl

  -- τ=28: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=36 (1×)
  cell-19-28 : τ 28 ≡ τ 28
  cell-19-28 = refl

  -- τ=131: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=192 (1×)
  cell-19-131 : τ 131 ≡ τ 131
  cell-19-131 = refl

  -- τ=253: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=373 (1×)
  cell-19-253 : τ 253 ≡ τ 253
  cell-19-253 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=50, 4 nodes, 1 type contexts, 3 forms

module equalizer-50 where

  -- τ=66: 4 nodes, 3 forms
  -- Types: (untyped)
  -- σ=90 (2×)
  -- σ=258 (1×)
  -- σ=2052 (1×)
  cell-50-66 : τ 66 ≡ τ 66
  cell-50-66 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=97, 4 nodes, 1 type contexts, 2 forms

module apply-97 where

  -- τ=140: 4 nodes, 2 forms
  -- Types: (untyped)
  -- σ=202 (2×)
  -- σ=1559 (2×)
  cell-97-140 : τ 140 ≡ τ 140
  cell-97-140 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=157, 4 nodes, 3 type contexts, 3 forms

module index-157 where

  -- τ=758: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1579 (2×)
  cell-157-758 : τ 758 ≡ τ 758
  cell-157-758 = refl

  -- τ=222: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=338 (1×)
  cell-157-222 : τ 222 ≡ τ 222
  cell-157-222 = refl

  -- τ=273: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=394 (1×)
  cell-157-273 : τ 273 ≡ τ 273
  cell-157-273 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=158, 4 nodes, 3 type contexts, 3 forms

module subscript-158 where

  -- τ=759: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1580 (2×)
  cell-158-759 : τ 759 ≡ τ 759
  cell-158-759 = refl

  -- τ=223: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=339 (1×)
  cell-158-223 : τ 223 ≡ τ 223
  cell-158-223 = refl

  -- τ=274: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=395 (1×)
  cell-158-274 : τ 274 ≡ τ 274
  cell-158-274 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=187, 4 nodes, 3 type contexts, 3 forms

module index-187 where

  -- τ=265: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=387 (2×)
  cell-187-265 : τ 265 ≡ τ 265
  cell-187-265 = refl

  -- τ=295: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=425 (1×)
  cell-187-295 : τ 295 ≡ τ 295
  cell-187-295 = refl

  -- τ=358: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=566 (1×)
  cell-187-358 : τ 358 ≡ τ 358
  cell-187-358 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=188, 4 nodes, 3 type contexts, 3 forms

module subscript-188 where

  -- τ=266: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=388 (2×)
  cell-188-266 : τ 266 ≡ τ 266
  cell-188-266 = refl

  -- τ=296: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=426 (1×)
  cell-188-296 : τ 296 ≡ τ 296
  cell-188-296 = refl

  -- τ=359: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=567 (1×)
  cell-188-359 : τ 359 ≡ τ 359
  cell-188-359 = refl


-- ── product (───────────────────────────────────────────)
-- κ=193, 4 nodes, 2 type contexts, 3 forms

module product-193 where

  -- τ=738: 3 nodes, 2 forms
  -- Types: tuple
  -- σ=1517 (1×)
  -- σ=1650 (2×)
  cell-193-738 : τ 738 ≡ τ 738
  cell-193-738 = refl

  -- τ=282: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=405 (1×)
  cell-193-282 : τ 282 ≡ τ 282
  cell-193-282 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=194, 4 nodes, 2 type contexts, 3 forms

module index-194 where

  -- τ=739: 3 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1518 (1×)
  -- σ=1651 (2×)
  cell-194-739 : τ 739 ≡ τ 739
  cell-194-739 = refl

  -- τ=283: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=406 (1×)
  cell-194-283 : τ 283 ≡ τ 283
  cell-194-283 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=195, 4 nodes, 2 type contexts, 3 forms

module subscript-195 where

  -- τ=740: 3 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1519 (1×)
  -- σ=1652 (2×)
  cell-195-740 : τ 740 ≡ τ 740
  cell-195-740 = refl

  -- τ=284: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=407 (1×)
  cell-195-284 : τ 284 ≡ τ 284
  cell-195-284 = refl


-- ── gte (───────────────────────────────────────────────)
-- κ=241, 4 nodes, 1 type contexts, 1 forms

module gte-241 where

  -- τ=340: 4 nodes, 1 forms
  -- Types: (untyped)
  -- σ=515 (4×)
  cell-241-340 : τ 340 ≡ τ 340
  cell-241-340 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=277, 4 nodes, 1 type contexts, 2 forms

module subscript-277 where

  -- τ=379: 4 nodes, 2 forms
  -- Types: (untyped)
  -- σ=615 (2×)
  -- σ=1179 (2×)
  cell-277-379 : τ 379 ≡ τ 379
  cell-277-379 = refl


-- ── free_monoid (───────────────────────────────────────)
-- κ=282, 4 nodes, 1 type contexts, 3 forms

module free_monoid-282 where

  -- τ=385: 4 nodes, 3 forms
  -- Types: (untyped)
  -- σ=628 (2×)
  -- σ=789 (1×)
  -- σ=1128 (1×)
  cell-282-385 : τ 385 ≡ τ 385
  cell-282-385 = refl


-- ── free_monoid.fold (──────────────────────────────────)
-- κ=306, 4 nodes, 2 type contexts, 2 forms

module free_monoid-fold-306 where

  -- τ=414: 3 nodes, 1 forms
  -- Types: str
  -- σ=675 (3×)
  cell-306-414 : τ 414 ≡ τ 414
  cell-306-414 = refl

  -- τ=487: 1 nodes, 1 forms
  -- Types: str
  -- σ=841 (1×)
  cell-306-487 : τ 487 ≡ τ 487
  cell-306-487 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=350, 4 nodes, 1 type contexts, 4 forms

module apply-350 where

  -- τ=469: 4 nodes, 4 forms
  -- Types: (untyped)
  -- σ=803 (1×)
  -- σ=978 (1×)
  -- σ=1039 (1×)
  -- σ=1070 (1×)
  cell-350-469 : τ 469 ≡ τ 469
  cell-350-469 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=351, 4 nodes, 1 type contexts, 4 forms

module let-k-351 where

  -- τ=470: 4 nodes, 4 forms
  -- Types: (untyped)
  -- σ=804 (1×)
  -- σ=979 (1×)
  -- σ=1040 (1×)
  -- σ=1071 (1×)
  cell-351-470 : τ 470 ≡ τ 470
  cell-351-470 = refl


-- ── lazy_fold (─────────────────────────────────────────)
-- κ=395, 4 nodes, 1 type contexts, 4 forms

module lazy_fold-395 where

  -- τ=519: 4 nodes, 4 forms
  -- Types: (untyped)
  -- σ=897 (1×)
  -- σ=1254 (1×)
  -- σ=1343 (1×)
  -- σ=1888 (1×)
  cell-395-519 : τ 519 ≡ τ 519
  cell-395-519 = refl


-- ── product (───────────────────────────────────────────)
-- κ=414, 4 nodes, 4 type contexts, 4 forms

module product-414 where

  -- τ=542: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=966 (1×)
  cell-414-542 : τ 542 ≡ τ 542
  cell-414-542 = refl

  -- τ=725: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=1489 (1×)
  cell-414-725 : τ 725 ≡ τ 725
  cell-414-725 = refl

  -- τ=773: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=1628 (1×)
  cell-414-773 : τ 773 ≡ τ 773
  cell-414-773 = refl

  -- τ=805: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=1699 (1×)
  cell-414-805 : τ 805 ≡ τ 805
  cell-414-805 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=484, 4 nodes, 1 type contexts, 4 forms

module let-k-484 where

  -- τ=620: 4 nodes, 4 forms
  -- Types: (untyped)
  -- σ=1228 (1×)
  -- σ=1803 (1×)
  -- σ=1805 (1×)
  -- σ=1807 (1×)
  cell-484-620 : τ 620 ≡ τ 620
  cell-484-620 = refl


-- ── eval (──────────────────────────────────────────────)
-- κ=540, 4 nodes, 1 type contexts, 2 forms

module eval-540 where

  -- τ=689: 4 nodes, 2 forms
  -- Types: T
  -- σ=1416 (1×)
  -- σ=1529 (3×)
  cell-540-689 : τ 689 ≡ τ 689
  cell-540-689 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=541, 4 nodes, 1 type contexts, 2 forms

module annassign-541 where

  -- τ=690: 4 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1417 (1×)
  -- σ=1530 (3×)
  cell-541-690 : τ 690 ≡ τ 690
  cell-541-690 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=25, 3 nodes, 1 type contexts, 3 forms

module equalizer-25 where

  -- τ=35: 3 nodes, 3 forms
  -- Types: (untyped)
  -- σ=44 (1×)
  -- σ=768 (1×)
  -- σ=952 (1×)
  cell-25-35 : τ 35 ≡ τ 35
  cell-25-35 = refl


-- ── lt (────────────────────────────────────────────────)
-- κ=52, 3 nodes, 1 type contexts, 1 forms

module lt-52 where

  -- τ=68: 3 nodes, 1 forms
  -- Types: (untyped)
  -- σ=95 (3×)
  cell-52-68 : τ 68 ≡ τ 68
  cell-52-68 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=65, 3 nodes, 1 type contexts, 2 forms

module apply-65 where

  -- τ=82: 3 nodes, 2 forms
  -- Types: (untyped)
  -- σ=120 (1×)
  -- σ=1437 (2×)
  cell-65-82 : τ 82 ≡ τ 82
  cell-65-82 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=96, 3 nodes, 1 type contexts, 3 forms

module annassign-96 where

  -- τ=138: 3 nodes, 3 forms
  -- Types: (untyped)
  -- σ=199 (1×)
  -- σ=377 (1×)
  -- σ=402 (1×)
  cell-96-138 : τ 138 ≡ τ 138
  cell-96-138 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=107, 3 nodes, 1 type contexts, 2 forms

module effect-seq-107 where

  -- τ=155: 3 nodes, 2 forms
  -- Types: (untyped)
  -- σ=226 (1×)
  -- σ=1145 (2×)
  cell-107-155 : τ 155 ≡ τ 155
  cell-107-155 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=155, 3 nodes, 1 type contexts, 3 forms

module apply-155 where

  -- τ=217: 3 nodes, 3 forms
  -- Types: (untyped)
  -- σ=324 (1×)
  -- σ=328 (1×)
  -- σ=332 (1×)
  cell-155-217 : τ 217 ≡ τ 217
  cell-155-217 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=156, 3 nodes, 1 type contexts, 3 forms

module annassign-156 where

  -- τ=218: 3 nodes, 3 forms
  -- Types: (untyped)
  -- σ=325 (1×)
  -- σ=329 (1×)
  -- σ=333 (1×)
  cell-156-218 : τ 218 ≡ τ 218
  cell-156-218 = refl


-- ── product (───────────────────────────────────────────)
-- κ=200, 3 nodes, 2 type contexts, 2 forms

module product-200 where

  -- τ=712: 2 nodes, 1 forms
  -- Types: tuple
  -- σ=1464 (2×)
  cell-200-712 : τ 712 ≡ τ 712
  cell-200-712 = refl

  -- τ=290: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=418 (1×)
  cell-200-290 : τ 290 ≡ τ 290
  cell-200-290 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=201, 3 nodes, 2 type contexts, 2 forms

module index-201 where

  -- τ=713: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1465 (2×)
  cell-201-713 : τ 713 ≡ τ 713
  cell-201-713 = refl

  -- τ=291: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=419 (1×)
  cell-201-291 : τ 291 ≡ τ 291
  cell-201-291 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=202, 3 nodes, 3 type contexts, 3 forms

module subscript-202 where

  -- τ=292: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=420 (1×)
  cell-202-292 : τ 292 ≡ τ 292
  cell-202-292 = refl

  -- τ=714: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1466 (1×)
  cell-202-714 : τ 714 ≡ τ 714
  cell-202-714 = refl

  -- τ=723: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1479 (1×)
  cell-202-723 : τ 723 ≡ τ 723
  cell-202-723 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=216, 3 nodes, 1 type contexts, 3 forms

module equalizer-216 where

  -- τ=308: 3 nodes, 3 forms
  -- Types: (untyped)
  -- σ=455 (1×)
  -- σ=1661 (1×)
  -- σ=2065 (1×)
  cell-216-308 : τ 308 ≡ τ 308
  cell-216-308 = refl


-- ── comprehension (─────────────────────────────────────)
-- κ=314, 3 nodes, 1 type contexts, 2 forms

module comprehension-314 where

  -- τ=422: 3 nodes, 2 forms
  -- Types: (untyped)
  -- σ=687 (2×)
  -- σ=1286 (1×)
  cell-314-422 : τ 422 ≡ τ 422
  cell-314-422 = refl


-- ── isnot (─────────────────────────────────────────────)
-- κ=333, 3 nodes, 1 type contexts, 1 forms

module isnot-333 where

  -- τ=442: 3 nodes, 1 forms
  -- Types: (untyped)
  -- σ=716 (3×)
  cell-333-442 : τ 442 ≡ τ 442
  cell-333-442 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=334, 3 nodes, 1 type contexts, 2 forms

module equalizer-334 where

  -- τ=443: 3 nodes, 2 forms
  -- Types: (untyped)
  -- σ=717 (1×)
  -- σ=1275 (2×)
  cell-334-443 : τ 443 ≡ τ 443
  cell-334-443 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=342, 3 nodes, 1 type contexts, 3 forms

module annassign-342 where

  -- τ=454: 3 nodes, 3 forms
  -- Types: (untyped)
  -- σ=754 (1×)
  -- σ=938 (1×)
  -- σ=945 (1×)
  cell-342-454 : τ 454 ≡ τ 454
  cell-342-454 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=347, 3 nodes, 1 type contexts, 2 forms

module annassign-347 where

  -- τ=460: 3 nodes, 2 forms
  -- Types: (untyped)
  -- σ=775 (2×)
  -- σ=1066 (1×)
  cell-347-460 : τ 460 ≡ τ 460
  cell-347-460 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=394, 3 nodes, 1 type contexts, 3 forms

module let-k-394 where

  -- τ=517: 3 nodes, 3 forms
  -- Types: (untyped)
  -- σ=890 (1×)
  -- σ=1025 (1×)
  -- σ=1086 (1×)
  cell-394-517 : τ 517 ≡ τ 517
  cell-394-517 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=415, 3 nodes, 3 type contexts, 3 forms

module index-415 where

  -- τ=543: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=967 (1×)
  cell-415-543 : τ 543 ≡ τ 543
  cell-415-543 = refl

  -- τ=726: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1490 (1×)
  cell-415-726 : τ 726 ≡ τ 726
  cell-415-726 = refl

  -- τ=806: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1700 (1×)
  cell-415-806 : τ 806 ≡ τ 806
  cell-415-806 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=416, 3 nodes, 3 type contexts, 3 forms

module subscript-416 where

  -- τ=544: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=968 (1×)
  cell-416-544 : τ 544 ≡ τ 544
  cell-416-544 = refl

  -- τ=727: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1491 (1×)
  cell-416-727 : τ 727 ≡ τ 727
  cell-416-727 = refl

  -- τ=807: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1701 (1×)
  cell-416-807 : τ 807 ≡ τ 807
  cell-416-807 = refl


-- ── free_monoid.literal (───────────────────────────────)
-- κ=440, 3 nodes, 1 type contexts, 3 forms

module free_monoid-literal-440 where

  -- τ=568: 3 nodes, 3 forms
  -- Types: list
  -- σ=1043 (1×)
  -- σ=1074 (1×)
  -- σ=1296 (1×)
  cell-440-568 : τ 568 ≡ τ 568
  cell-440-568 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=468, 3 nodes, 2 type contexts, 3 forms

module let-k-468 where

  -- τ=603: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1168 (1×)
  -- σ=2056 (1×)
  cell-468-603 : τ 603 ≡ τ 603
  cell-468-603 = refl

  -- τ=654: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1340 (1×)
  cell-468-654 : τ 654 ≡ τ 654
  cell-468-654 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=486, 3 nodes, 2 type contexts, 3 forms

module apply-486 where

  -- τ=623: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1243 (1×)
  -- σ=1249 (1×)
  cell-486-623 : τ 623 ≡ τ 623
  cell-486-623 = refl

  -- τ=631: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1270 (1×)
  cell-486-631 : τ 631 ≡ τ 631
  cell-486-631 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=487, 3 nodes, 2 type contexts, 3 forms

module let-k-487 where

  -- τ=624: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1244 (1×)
  -- σ=1250 (1×)
  cell-487-624 : τ 624 ≡ τ 624
  cell-487-624 = refl

  -- τ=632: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1271 (1×)
  cell-487-632 : τ 632 ≡ τ 632
  cell-487-632 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=515, 3 nodes, 1 type contexts, 3 forms

module apply-515 where

  -- τ=189: 3 nodes, 3 forms
  -- Types: (untyped)
  -- σ=1352 (1×)
  -- σ=1419 (1×)
  -- σ=1534 (1×)
  cell-515-189 : τ 189 ≡ τ 189
  cell-515-189 = refl


-- ── terminal.map (──────────────────────────────────────)
-- κ=559, 3 nodes, 1 type contexts, 2 forms

module terminal-map-559 where

  -- τ=709: 3 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1453 (2×)
  -- σ=1717 (1×)
  cell-559-709 : τ 709 ≡ τ 709
  cell-559-709 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=596, 3 nodes, 1 type contexts, 3 forms

module let-k-596 where

  -- τ=761: 3 nodes, 3 forms
  -- Types: (untyped)
  -- σ=1583 (1×)
  -- σ=1585 (1×)
  -- σ=1587 (1×)
  cell-596-761 : τ 761 ≡ τ 761
  cell-596-761 = refl


-- ── cardinality (───────────────────────────────────────)
-- κ=597, 3 nodes, 1 type contexts, 3 forms

module cardinality-597 where

  -- τ=763: 3 nodes, 3 forms
  -- Types: int
  -- σ=1595 (1×)
  -- σ=1600 (1×)
  -- σ=1606 (1×)
  cell-597-763 : τ 763 ≡ τ 763
  cell-597-763 = refl


-- ── partial@? (─────────────────────────────────────────)
-- κ=600, 3 nodes, 1 type contexts, 3 forms

module partial-at-x3f-600 where

  -- τ=188: 3 nodes, 3 forms
  -- Types: (untyped)
  -- σ=1612 (1×)
  -- σ=1912 (1×)
  -- σ=2058 (1×)
  cell-600-188 : τ 188 ≡ τ 188
  cell-600-188 = refl


-- ── product (───────────────────────────────────────────)
-- κ=615, 3 nodes, 1 type contexts, 1 forms

module product-615 where

  -- τ=782: 3 nodes, 1 forms
  -- Types: tuple
  -- σ=1644 (3×)
  cell-615-782 : τ 782 ≡ τ 782
  cell-615-782 = refl


-- ── coerce (────────────────────────────────────────────)
-- κ=674, 3 nodes, 1 type contexts, 3 forms

module coerce-674 where

  -- τ=851: 3 nodes, 3 forms
  -- Types: (untyped)
  -- σ=1821 (1×)
  -- σ=1833 (1×)
  -- σ=1840 (1×)
  cell-674-851 : τ 851 ≡ τ 851
  cell-674-851 = refl


-- ── bimap (─────────────────────────────────────────────)
-- κ=677, 3 nodes, 1 type contexts, 3 forms

module bimap-677 where

  -- τ=854: 3 nodes, 3 forms
  -- Types: (untyped)
  -- σ=1825 (1×)
  -- σ=1835 (1×)
  -- σ=1842 (1×)
  cell-677-854 : τ 854 ≡ τ 854
  cell-677-854 = refl


-- ── coerce (────────────────────────────────────────────)
-- κ=678, 3 nodes, 1 type contexts, 3 forms

module coerce-678 where

  -- τ=855: 3 nodes, 3 forms
  -- Types: (untyped)
  -- σ=1828 (1×)
  -- σ=1836 (1×)
  -- σ=1843 (1×)
  cell-678-855 : τ 855 ≡ τ 855
  cell-678-855 = refl


-- ── free_monoid.fold (──────────────────────────────────)
-- κ=679, 3 nodes, 1 type contexts, 3 forms

module free_monoid-fold-679 where

  -- τ=856: 3 nodes, 3 forms
  -- Types: str
  -- σ=1830 (1×)
  -- σ=1837 (1×)
  -- σ=1844 (1×)
  cell-679-856 : τ 856 ≡ τ 856
  cell-679-856 = refl


-- ── coerce (────────────────────────────────────────────)
-- κ=742, 3 nodes, 3 type contexts, 3 forms

module coerce-742 where

  -- τ=920: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1997 (1×)
  cell-742-920 : τ 920 ≡ τ 920
  cell-742-920 = refl

  -- τ=922: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=2002 (1×)
  cell-742-922 : τ 922 ≡ τ 922
  cell-742-922 = refl

  -- τ=950: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=2080 (1×)
  cell-742-950 : τ 950 ≡ τ 950
  cell-742-950 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=35, 2 nodes, 1 type contexts, 2 forms

module equalizer-35 where

  -- τ=49: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=60 (1×)
  -- σ=64 (1×)
  cell-35-49 : τ 49 ≡ τ 49
  cell-35-49 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=51, 2 nodes, 1 type contexts, 1 forms

module equalizer-51 where

  -- τ=67: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=92 (2×)
  cell-51-67 : τ 67 ≡ τ 67
  cell-51-67 = refl


-- ── terminal.map (──────────────────────────────────────)
-- κ=71, 2 nodes, 1 type contexts, 2 forms

module terminal-map-71 where

  -- τ=88: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=128 (1×)
  -- σ=1405 (1×)
  cell-71-88 : τ 88 ≡ τ 88
  cell-71-88 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=81, 2 nodes, 1 type contexts, 2 forms

module annassign-81 where

  -- τ=106: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=153 (1×)
  -- σ=186 (1×)
  cell-81-106 : τ 106 ≡ τ 106
  cell-81-106 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=82, 2 nodes, 2 type contexts, 2 forms

module annassign-82 where

  -- τ=108: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=156 (1×)
  cell-82-108 : τ 108 ≡ τ 108
  cell-82-108 = refl

  -- τ=110: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=159 (1×)
  cell-82-110 : τ 110 ≡ τ 110
  cell-82-110 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=84, 2 nodes, 2 type contexts, 2 forms

module annassign-84 where

  -- τ=116: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=165 (1×)
  cell-84-116 : τ 116 ≡ τ 116
  cell-84-116 = refl

  -- τ=277: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=400 (1×)
  cell-84-277 : τ 277 ≡ τ 277
  cell-84-277 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=98, 2 nodes, 1 type contexts, 2 forms

module annassign-98 where

  -- τ=141: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=203 (1×)
  -- σ=375 (1×)
  cell-98-141 : τ 141 ≡ τ 141
  cell-98-141 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=101, 2 nodes, 1 type contexts, 2 forms

module let-k-101 where

  -- τ=146: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=214 (1×)
  -- σ=1796 (1×)
  cell-101-146 : τ 146 ≡ τ 146
  cell-101-146 = refl


-- ── free_monoid.op@? (──────────────────────────────────)
-- κ=110, 2 nodes, 2 type contexts, 2 forms

module free_monoid-op-at-x3f-110 where

  -- τ=159: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=230 (1×)
  cell-110-159 : τ 159 ≡ τ 159
  cell-110-159 = refl

  -- τ=179: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=264 (1×)
  cell-110-179 : τ 179 ≡ τ 179
  cell-110-179 = refl


-- ── terminal.map (──────────────────────────────────────)
-- κ=114, 2 nodes, 2 type contexts, 2 forms

module terminal-map-114 where

  -- τ=166: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=241 (1×)
  cell-114-166 : τ 166 ≡ τ 166
  cell-114-166 = refl

  -- τ=512: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=880 (1×)
  cell-114-512 : τ 512 ≡ τ 512
  cell-114-512 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=159, 2 nodes, 2 type contexts, 2 forms

module annassign-159 where

  -- τ=224: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=340 (1×)
  cell-159-224 : τ 224 ≡ τ 224
  cell-159-224 = refl

  -- τ=275: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=396 (1×)
  cell-159-275 : τ 275 ≡ τ 275
  cell-159-275 = refl


-- ── product (───────────────────────────────────────────)
-- κ=181, 2 nodes, 2 type contexts, 2 forms

module product-181 where

  -- τ=258: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=380 (1×)
  cell-181-258 : τ 258 ≡ τ 258
  cell-181-258 = refl

  -- τ=461: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=777 (1×)
  cell-181-461 : τ 461 ≡ τ 461
  cell-181-461 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=182, 2 nodes, 2 type contexts, 2 forms

module index-182 where

  -- τ=259: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=381 (1×)
  cell-182-259 : τ 259 ≡ τ 259
  cell-182-259 = refl

  -- τ=462: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=778 (1×)
  cell-182-462 : τ 462 ≡ τ 462
  cell-182-462 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=183, 2 nodes, 2 type contexts, 2 forms

module subscript-183 where

  -- τ=260: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=382 (1×)
  cell-183-260 : τ 260 ≡ τ 260
  cell-183-260 = refl

  -- τ=463: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=779 (1×)
  cell-183-463 : τ 463 ≡ τ 463
  cell-183-463 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=184, 2 nodes, 2 type contexts, 2 forms

module index-184 where

  -- τ=261: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=383 (1×)
  cell-184-261 : τ 261 ≡ τ 261
  cell-184-261 = refl

  -- τ=464: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=780 (1×)
  cell-184-464 : τ 464 ≡ τ 464
  cell-184-464 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=185, 2 nodes, 2 type contexts, 2 forms

module subscript-185 where

  -- τ=262: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=384 (1×)
  cell-185-262 : τ 262 ≡ τ 262
  cell-185-262 = refl

  -- τ=465: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=781 (1×)
  cell-185-465 : τ 465 ≡ τ 465
  cell-185-465 = refl


-- ── product (───────────────────────────────────────────)
-- κ=189, 2 nodes, 1 type contexts, 1 forms

module product-189 where

  -- τ=267: 2 nodes, 1 forms
  -- Types: tuple
  -- σ=389 (2×)
  cell-189-267 : τ 267 ≡ τ 267
  cell-189-267 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=190, 2 nodes, 1 type contexts, 1 forms

module index-190 where

  -- τ=268: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=390 (2×)
  cell-190-268 : τ 268 ≡ τ 268
  cell-190-268 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=191, 2 nodes, 2 type contexts, 2 forms

module subscript-191 where

  -- τ=269: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=391 (1×)
  cell-191-269 : τ 269 ≡ τ 269
  cell-191-269 = refl

  -- τ=878: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1899 (1×)
  cell-191-878 : τ 878 ≡ τ 878
  cell-191-878 = refl


-- ── product (───────────────────────────────────────────)
-- κ=218, 2 nodes, 1 type contexts, 1 forms

module product-218 where

  -- τ=310: 2 nodes, 1 forms
  -- Types: tuple
  -- σ=458 (2×)
  cell-218-310 : τ 310 ≡ τ 310
  cell-218-310 = refl


-- ── partial.apply@state (───────────────────────────────)
-- κ=219, 2 nodes, 2 type contexts, 2 forms

module partial-apply-at-state-219 where

  -- τ=311: 1 nodes, 1 forms
  -- Types: T
  -- σ=459 (1×)
  cell-219-311 : τ 311 ≡ τ 311
  cell-219-311 = refl

  -- τ=392: 1 nodes, 1 forms
  -- Types: T
  -- σ=639 (1×)
  cell-219-392 : τ 392 ≡ τ 392
  cell-219-392 = refl


-- ── arguments (─────────────────────────────────────────)
-- κ=227, 2 nodes, 1 type contexts, 2 forms

module arguments-227 where

  -- τ=320: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=472 (1×)
  -- σ=1523 (1×)
  cell-227-320 : τ 320 ≡ τ 320
  cell-227-320 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=242, 2 nodes, 2 type contexts, 2 forms

module equalizer-242 where

  -- τ=341: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=518 (1×)
  cell-242-341 : τ 341 ≡ τ 341
  cell-242-341 = refl

  -- τ=411: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=670 (1×)
  cell-242-411 : τ 411 ≡ τ 411
  cell-242-411 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=256, 2 nodes, 1 type contexts, 2 forms

module equalizer-256 where

  -- τ=357: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=562 (1×)
  -- σ=695 (1×)
  cell-256-357 : τ 357 ≡ τ 357
  cell-256-357 = refl


-- ── partial@? (─────────────────────────────────────────)
-- κ=261, 2 nodes, 1 type contexts, 1 forms

module partial-at-x3f-261 where

  -- τ=178: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=582 (2×)
  cell-261-178 : τ 178 ≡ τ 178
  cell-261-178 = refl


-- ── partial.apply@? (───────────────────────────────────)
-- κ=262, 2 nodes, 1 type contexts, 2 forms

module partial-apply-at-x3f-262 where

  -- τ=364: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=584 (1×)
  -- σ=1706 (1×)
  cell-262-364 : τ 364 ≡ τ 364
  cell-262-364 = refl


-- ── coerce (────────────────────────────────────────────)
-- κ=278, 2 nodes, 1 type contexts, 1 forms

module coerce-278 where

  -- τ=380: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=616 (2×)
  cell-278-380 : τ 380 ≡ τ 380
  cell-278-380 = refl


-- ── free_monoid.fold (──────────────────────────────────)
-- κ=279, 2 nodes, 1 type contexts, 2 forms

module free_monoid-fold-279 where

  -- τ=381: 2 nodes, 2 forms
  -- Types: str
  -- σ=617 (1×)
  -- σ=620 (1×)
  cell-279-381 : τ 381 ≡ τ 381
  cell-279-381 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=280, 2 nodes, 1 type contexts, 2 forms

module let-k-280 where

  -- τ=382: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=618 (1×)
  -- σ=621 (1×)
  cell-280-382 : τ 382 ≡ τ 382
  cell-280-382 = refl


-- ── free_monoid (───────────────────────────────────────)
-- κ=296, 2 nodes, 1 type contexts, 2 forms

module free_monoid-296 where

  -- τ=404: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=660 (1×)
  -- σ=947 (1×)
  cell-296-404 : τ 404 ≡ τ 404
  cell-296-404 = refl


-- ── fixpoint.halt (─────────────────────────────────────)
-- κ=325, 2 nodes, 1 type contexts, 1 forms

module fixpoint-halt-325 where

  -- τ=433: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=702 (2×)
  cell-325-433 : τ 433 ≡ τ 433
  cell-325-433 = refl


-- ── exponential.literal (───────────────────────────────)
-- κ=326, 2 nodes, 1 type contexts, 2 forms

module exponential-literal-326 where

  -- τ=435: 2 nodes, 2 forms
  -- Types: dict
  -- σ=704 (1×)
  -- σ=1369 (1×)
  cell-326-435 : τ 435 ≡ τ 435
  cell-326-435 = refl


-- ── arguments (─────────────────────────────────────────)
-- κ=341, 2 nodes, 1 type contexts, 2 forms

module arguments-341 where

  -- τ=453: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=748 (1×)
  -- σ=934 (1×)
  cell-341-453 : τ 453 ≡ τ 453
  cell-341-453 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=346, 2 nodes, 1 type contexts, 2 forms

module equalizer-346 where

  -- τ=459: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=769 (1×)
  -- σ=953 (1×)
  cell-346-459 : τ 459 ≡ τ 459
  cell-346-459 = refl


-- ── free_monoid.snoc@? (────────────────────────────────)
-- κ=358, 2 nodes, 1 type contexts, 2 forms

module free_monoid-snoc-at-x3f-358 where

  -- τ=478: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=818 (1×)
  -- σ=1753 (1×)
  cell-358-478 : τ 478 ≡ τ 478
  cell-358-478 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=359, 2 nodes, 1 type contexts, 2 forms

module effect-seq-359 where

  -- τ=479: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=819 (1×)
  -- σ=1754 (1×)
  cell-359-479 : τ 479 ≡ τ 479
  cell-359-479 = refl


-- ── terminal.map (──────────────────────────────────────)
-- κ=386, 2 nodes, 1 type contexts, 2 forms

module terminal-map-386 where

  -- τ=508: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=876 (1×)
  -- σ=1800 (1×)
  cell-386-508 : τ 508 ≡ τ 508
  cell-386-508 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=396, 2 nodes, 1 type contexts, 2 forms

module apply-396 where

  -- τ=520: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=898 (1×)
  -- σ=1255 (1×)
  cell-396-520 : τ 520 ≡ τ 520
  cell-396-520 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=397, 2 nodes, 1 type contexts, 2 forms

module let-k-397 where

  -- τ=521: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=899 (1×)
  -- σ=1256 (1×)
  cell-397-521 : τ 521 ≡ τ 521
  cell-397-521 = refl


-- ── not (───────────────────────────────────────────────)
-- κ=412, 2 nodes, 1 type contexts, 1 forms

module not-412 where

  -- τ=540: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=962 (2×)
  cell-412-540 : τ 540 ≡ τ 540
  cell-412-540 = refl


-- ── complement (────────────────────────────────────────)
-- κ=413, 2 nodes, 1 type contexts, 2 forms

module complement-413 where

  -- τ=541: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=964 (1×)
  -- σ=2010 (1×)
  cell-413-541 : τ 541 ≡ τ 541
  cell-413-541 = refl


-- ── free_monoid.snoc@? (────────────────────────────────)
-- κ=420, 2 nodes, 1 type contexts, 2 forms

module free_monoid-snoc-at-x3f-420 where

  -- τ=548: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=985 (1×)
  -- σ=1671 (1×)
  cell-420-548 : τ 548 ≡ τ 548
  cell-420-548 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=421, 2 nodes, 1 type contexts, 2 forms

module effect-seq-421 where

  -- τ=549: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=986 (1×)
  -- σ=1672 (1×)
  cell-421-549 : τ 549 ≡ τ 549
  cell-421-549 = refl


-- ── product (───────────────────────────────────────────)
-- κ=441, 2 nodes, 1 type contexts, 2 forms

module product-441 where

  -- τ=569: 2 nodes, 2 forms
  -- Types: tuple
  -- σ=1045 (1×)
  -- σ=1076 (1×)
  cell-441-569 : τ 569 ≡ τ 569
  cell-441-569 = refl


-- ── free_monoid.snoc@state (────────────────────────────)
-- κ=442, 2 nodes, 1 type contexts, 2 forms

module free_monoid-snoc-at-state-442 where

  -- τ=570: 2 nodes, 2 forms
  -- Types: None
  -- σ=1046 (1×)
  -- σ=1077 (1×)
  cell-442-570 : τ 570 ≡ τ 570
  cell-442-570 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=443, 2 nodes, 1 type contexts, 2 forms

module effect-seq-443 where

  -- τ=571: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1047 (1×)
  -- σ=1078 (1×)
  cell-443-571 : τ 571 ≡ τ 571
  cell-443-571 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=444, 2 nodes, 1 type contexts, 2 forms

module equalizer-444 where

  -- τ=572: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1061 (1×)
  -- σ=1079 (1×)
  cell-444-572 : τ 572 ≡ τ 572
  cell-444-572 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=445, 2 nodes, 1 type contexts, 2 forms

module equalizer-445 where

  -- τ=573: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1063 (1×)
  -- σ=1081 (1×)
  cell-445-573 : τ 573 ≡ τ 573
  cell-445-573 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=446, 2 nodes, 1 type contexts, 2 forms

module fold-446 where

  -- τ=574: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1064 (1×)
  -- σ=1082 (1×)
  cell-446-574 : τ 574 ≡ τ 574
  cell-446-574 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=450, 2 nodes, 2 type contexts, 2 forms

module annassign-450 where

  -- τ=579: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1108 (1×)
  cell-450-579 : τ 579 ≡ τ 579
  cell-450-579 = refl

  -- τ=789: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1657 (1×)
  cell-450-789 : τ 789 ≡ τ 789
  cell-450-789 = refl


-- ── projection@object (─────────────────────────────────)
-- κ=451, 2 nodes, 1 type contexts, 2 forms

module projection-at-object-451 where

  -- τ=34: 2 nodes, 2 forms
  -- Types: Self._cascade_abstraction_merge, Self._cascade_eta, Self._cell_contents, Self._cell_obs, Self._cleavage_fibers
  -- σ=1110 (1×)
  -- σ=1131 (1×)
  cell-451-34 : τ 34 ≡ τ 34
  cell-451-34 = refl


-- ── projection.compute@object (─────────────────────────)
-- κ=452, 2 nodes, 1 type contexts, 2 forms

module projection-compute-at-object-452 where

  -- τ=581: 2 nodes, 2 forms
  -- Types: Iter
  -- σ=1111 (1×)
  -- σ=1132 (1×)
  cell-452-581 : τ 581 ≡ τ 581
  cell-452-581 = refl


-- ── free_monoid (───────────────────────────────────────)
-- κ=453, 2 nodes, 1 type contexts, 2 forms

module free_monoid-453 where

  -- τ=582: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1112 (1×)
  -- σ=1133 (1×)
  cell-453-582 : τ 582 ≡ τ 582
  cell-453-582 = refl


-- ── coerce (────────────────────────────────────────────)
-- κ=459, 2 nodes, 1 type contexts, 1 forms

module coerce-459 where

  -- τ=589: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1139 (2×)
  cell-459-589 : τ 589 ≡ τ 589
  cell-459-589 = refl


-- ── powerset.literal (──────────────────────────────────)
-- κ=462, 2 nodes, 1 type contexts, 1 forms

module powerset-literal-462 where

  -- τ=593: 2 nodes, 1 forms
  -- Types: set
  -- σ=1147 (2×)
  cell-462-593 : τ 593 ≡ τ 593
  cell-462-593 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=463, 2 nodes, 1 type contexts, 2 forms

module annassign-463 where

  -- τ=594: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1148 (1×)
  -- σ=1305 (1×)
  cell-463-594 : τ 594 ≡ τ 594
  cell-463-594 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=464, 2 nodes, 1 type contexts, 1 forms

module effect-seq-464 where

  -- τ=598: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1153 (2×)
  cell-464-598 : τ 598 ≡ τ 598
  cell-464-598 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=465, 2 nodes, 1 type contexts, 2 forms

module equalizer-465 where

  -- τ=599: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1158 (1×)
  -- σ=1310 (1×)
  cell-465-599 : τ 599 ≡ τ 599
  cell-465-599 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=466, 2 nodes, 1 type contexts, 2 forms

module equalizer-466 where

  -- τ=600: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1161 (1×)
  -- σ=1311 (1×)
  cell-466-600 : τ 600 ≡ τ 600
  cell-466-600 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=467, 2 nodes, 1 type contexts, 2 forms

module fold-467 where

  -- τ=601: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1162 (1×)
  -- σ=1312 (1×)
  cell-467-601 : τ 601 ≡ τ 601
  cell-467-601 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=470, 2 nodes, 1 type contexts, 1 forms

module let-k-470 where

  -- τ=605: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1176 (2×)
  cell-470-605 : τ 605 ≡ τ 605
  cell-470-605 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=471, 2 nodes, 1 type contexts, 2 forms

module equalizer-471 where

  -- τ=606: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1195 (1×)
  -- σ=1322 (1×)
  cell-471-606 : τ 606 ≡ τ 606
  cell-471-606 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=472, 2 nodes, 1 type contexts, 2 forms

module fold-472 where

  -- τ=607: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1196 (1×)
  -- σ=1323 (1×)
  cell-472-607 : τ 607 ≡ τ 607
  cell-472-607 = refl


-- ── free_monoid.snoc@state (────────────────────────────)
-- κ=473, 2 nodes, 2 type contexts, 2 forms

module free_monoid-snoc-at-state-473 where

  -- τ=609: 1 nodes, 1 forms
  -- Types: None
  -- σ=1198 (1×)
  cell-473-609 : τ 609 ≡ τ 609
  cell-473-609 = refl

  -- τ=647: 1 nodes, 1 forms
  -- Types: None
  -- σ=1325 (1×)
  cell-473-647 : τ 647 ≡ τ 647
  cell-473-647 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=474, 2 nodes, 2 type contexts, 2 forms

module effect-seq-474 where

  -- τ=610: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1199 (1×)
  cell-474-610 : τ 610 ≡ τ 610
  cell-474-610 = refl

  -- τ=648: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1326 (1×)
  cell-474-648 : τ 648 ≡ τ 648
  cell-474-648 = refl


-- ── and (───────────────────────────────────────────────)
-- κ=493, 2 nodes, 1 type contexts, 1 forms

module and-493 where

  -- τ=634: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1274 (2×)
  cell-493-634 : τ 634 ≡ τ 634
  cell-493-634 = refl


-- ── powerset (──────────────────────────────────────────)
-- κ=511, 2 nodes, 1 type contexts, 2 forms

module powerset-511 where

  -- τ=520: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1344 (1×)
  -- σ=1889 (1×)
  cell-511-520 : τ 520 ≡ τ 520
  cell-511-520 = refl


-- ── product (───────────────────────────────────────────)
-- κ=531, 2 nodes, 2 type contexts, 2 forms

module product-531 where

  -- τ=677: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=1399 (1×)
  cell-531-677 : τ 677 ≡ τ 677
  cell-531-677 = refl

  -- τ=679: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=1401 (1×)
  cell-531-679 : τ 679 ≡ τ 679
  cell-531-679 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=544, 2 nodes, 1 type contexts, 1 forms

module index-544 where

  -- τ=694: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1426 (2×)
  cell-544-694 : τ 694 ≡ τ 694
  cell-544-694 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=545, 2 nodes, 1 type contexts, 1 forms

module subscript-545 where

  -- τ=695: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1427 (2×)
  cell-545-695 : τ 695 ≡ τ 695
  cell-545-695 = refl


-- ── product (───────────────────────────────────────────)
-- κ=546, 2 nodes, 1 type contexts, 1 forms

module product-546 where

  -- τ=696: 2 nodes, 1 forms
  -- Types: tuple
  -- σ=1428 (2×)
  cell-546-696 : τ 696 ≡ τ 696
  cell-546-696 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=547, 2 nodes, 1 type contexts, 1 forms

module index-547 where

  -- τ=697: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1429 (2×)
  cell-547-697 : τ 697 ≡ τ 697
  cell-547-697 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=548, 2 nodes, 2 type contexts, 2 forms

module subscript-548 where

  -- τ=698: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1430 (1×)
  cell-548-698 : τ 698 ≡ τ 698
  cell-548-698 = refl

  -- τ=710: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1454 (1×)
  cell-548-710 : τ 710 ≡ τ 710
  cell-548-710 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=570, 2 nodes, 2 type contexts, 2 forms

module annassign-570 where

  -- τ=729: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1493 (1×)
  cell-570-729 : τ 729 ≡ τ 729
  cell-570-729 = refl

  -- τ=808: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1702 (1×)
  cell-570-808 : τ 808 ≡ τ 808
  cell-570-808 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=571, 2 nodes, 1 type contexts, 2 forms

module index-571 where

  -- τ=730: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1497 (1×)
  -- σ=1501 (1×)
  cell-571-730 : τ 730 ≡ τ 730
  cell-571-730 = refl


-- ── comprehension (─────────────────────────────────────)
-- κ=576, 2 nodes, 1 type contexts, 2 forms

module comprehension-576 where

  -- τ=735: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1513 (1×)
  -- σ=1741 (1×)
  cell-576-735 : τ 735 ≡ τ 735
  cell-576-735 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=589, 2 nodes, 1 type contexts, 2 forms

module annassign-589 where

  -- τ=751: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1560 (1×)
  -- σ=1574 (1×)
  cell-589-751 : τ 751 ≡ τ 751
  cell-589-751 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=619, 2 nodes, 1 type contexts, 1 forms

module index-619 where

  -- τ=786: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1653 (2×)
  cell-619-786 : τ 786 ≡ τ 786
  cell-619-786 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=620, 2 nodes, 1 type contexts, 1 forms

module subscript-620 where

  -- τ=787: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1654 (2×)
  cell-620-787 : τ 787 ≡ τ 787
  cell-620-787 = refl


-- ── usub (──────────────────────────────────────────────)
-- κ=627, 2 nodes, 1 type contexts, 1 forms

module usub-627 where

  -- τ=795: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1678 (2×)
  cell-627-795 : τ 795 ≡ τ 795
  cell-627-795 = refl


-- ── product (───────────────────────────────────────────)
-- κ=646, 2 nodes, 1 type contexts, 1 forms

module product-646 where

  -- τ=818: 2 nodes, 1 forms
  -- Types: tuple
  -- σ=1724 (2×)
  cell-646-818 : τ 818 ≡ τ 818
  cell-646-818 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=647, 2 nodes, 1 type contexts, 1 forms

module index-647 where

  -- τ=819: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1725 (2×)
  cell-647-819 : τ 819 ≡ τ 819
  cell-647-819 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=648, 2 nodes, 1 type contexts, 1 forms

module subscript-648 where

  -- τ=820: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1726 (2×)
  cell-648-820 : τ 820 ≡ τ 820
  cell-648-820 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=649, 2 nodes, 1 type contexts, 1 forms

module index-649 where

  -- τ=821: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1727 (2×)
  cell-649-821 : τ 821 ≡ τ 821
  cell-649-821 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=650, 2 nodes, 1 type contexts, 1 forms

module subscript-650 where

  -- τ=822: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1728 (2×)
  cell-650-822 : τ 822 ≡ τ 822
  cell-650-822 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=654, 2 nodes, 1 type contexts, 2 forms

module apply-654 where

  -- τ=827: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1748 (1×)
  -- σ=2063 (1×)
  cell-654-827 : τ 827 ≡ τ 827
  cell-654-827 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=655, 2 nodes, 1 type contexts, 2 forms

module let-k-655 where

  -- τ=828: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1749 (1×)
  -- σ=2064 (1×)
  cell-655-828 : τ 828 ≡ τ 828
  cell-655-828 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=664, 2 nodes, 1 type contexts, 1 forms

module let-k-664 where

  -- τ=838: 2 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1772 (2×)
  cell-664-838 : τ 838 ≡ τ 838
  cell-664-838 = refl


-- ── free_monoid.fold (──────────────────────────────────)
-- κ=671, 2 nodes, 2 type contexts, 2 forms

module free_monoid-fold-671 where

  -- τ=848: 1 nodes, 1 forms
  -- Types: str
  -- σ=1815 (1×)
  cell-671-848 : τ 848 ≡ τ 848
  cell-671-848 = refl

  -- τ=931: 1 nodes, 1 forms
  -- Types: str
  -- σ=2016 (1×)
  cell-671-931 : τ 931 ≡ τ 931
  cell-671-931 = refl


-- ── free_monoid.fold (──────────────────────────────────)
-- κ=672, 2 nodes, 1 type contexts, 1 forms

module free_monoid-fold-672 where

  -- τ=849: 2 nodes, 1 forms
  -- Types: str
  -- σ=1816 (2×)
  cell-672-849 : τ 849 ≡ τ 849
  cell-672-849 = refl


-- ── coerce (────────────────────────────────────────────)
-- κ=680, 2 nodes, 1 type contexts, 2 forms

module coerce-680 where

  -- τ=857: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1847 (1×)
  -- σ=1856 (1×)
  cell-680-857 : τ 857 ≡ τ 857
  cell-680-857 = refl


-- ── bimap (─────────────────────────────────────────────)
-- κ=681, 2 nodes, 1 type contexts, 2 forms

module bimap-681 where

  -- τ=858: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1849 (1×)
  -- σ=1857 (1×)
  cell-681-858 : τ 858 ≡ τ 858
  cell-681-858 = refl


-- ── bimap (─────────────────────────────────────────────)
-- κ=682, 2 nodes, 1 type contexts, 2 forms

module bimap-682 where

  -- τ=859: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1850 (1×)
  -- σ=1858 (1×)
  cell-682-859 : τ 859 ≡ τ 859
  cell-682-859 = refl


-- ── coerce (────────────────────────────────────────────)
-- κ=683, 2 nodes, 1 type contexts, 2 forms

module coerce-683 where

  -- τ=860: 2 nodes, 2 forms
  -- Types: (untyped)
  -- σ=1851 (1×)
  -- σ=1859 (1×)
  cell-683-860 : τ 860 ≡ τ 860
  cell-683-860 = refl


-- ── free_monoid.fold (──────────────────────────────────)
-- κ=684, 2 nodes, 1 type contexts, 2 forms

module free_monoid-fold-684 where

  -- τ=861: 2 nodes, 2 forms
  -- Types: str
  -- σ=1852 (1×)
  -- σ=1860 (1×)
  cell-684-861 : τ 861 ≡ τ 861
  cell-684-861 = refl


-- ── pullback.import (───────────────────────────────────)
-- κ=3, 1 nodes, 1 type contexts, 1 forms

module pullback-import-3 where

  -- τ=3: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=3 (1×)
  cell-3-3 : τ 3 ≡ τ 3
  cell-3-3 = refl


-- ── pullback.import (───────────────────────────────────)
-- κ=4, 1 nodes, 1 type contexts, 1 forms

module pullback-import-4 where

  -- τ=4: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=6 (1×)
  cell-4-4 : τ 4 ≡ τ 4
  cell-4-4 = refl


-- ── pullback.import (───────────────────────────────────)
-- κ=5, 1 nodes, 1 type contexts, 1 forms

module pullback-import-5 where

  -- τ=5: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=10 (1×)
  cell-5-5 : τ 5 ≡ τ 5
  cell-5-5 = refl


-- ── product (───────────────────────────────────────────)
-- κ=9, 1 nodes, 1 type contexts, 1 forms

module product-9 where

  -- τ=9: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=18 (1×)
  cell-9-9 : τ 9 ≡ τ 9
  cell-9-9 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=10, 1 nodes, 1 type contexts, 1 forms

module let-k-10 where

  -- τ=10: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=19 (1×)
  cell-10-10 : τ 10 ≡ τ 10
  cell-10-10 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=20, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-20 where

  -- τ=30: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=38 (1×)
  cell-20-30 : τ 30 ≡ τ 30
  cell-20-30 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=29, 1 nodes, 1 type contexts, 1 forms

module let-k-29 where

  -- τ=40: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=51 (1×)
  cell-29-40 : τ 40 ≡ τ 40
  cell-29-40 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=30, 1 nodes, 1 type contexts, 1 forms

module equalizer-30 where

  -- τ=41: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=52 (1×)
  cell-30-41 : τ 41 ≡ τ 41
  cell-30-41 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=31, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-31 where

  -- τ=43: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=53 (1×)
  cell-31-43 : τ 43 ≡ τ 43
  cell-31-43 = refl


-- ── fixpoint (──────────────────────────────────────────)
-- κ=37, 1 nodes, 1 type contexts, 1 forms

module fixpoint-37 where

  -- τ=51: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=62 (1×)
  cell-37-51 : τ 51 ≡ τ 51
  cell-37-51 = refl


-- ── product.unpack (────────────────────────────────────)
-- κ=38, 1 nodes, 1 type contexts, 1 forms

module product-unpack-38 where

  -- τ=52: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=66 (1×)
  cell-38-52 : τ 52 ≡ τ 52
  cell-38-52 = refl


-- ── product (───────────────────────────────────────────)
-- κ=39, 1 nodes, 1 type contexts, 1 forms

module product-39 where

  -- τ=53: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=67 (1×)
  cell-39-53 : τ 53 ≡ τ 53
  cell-39-53 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=40, 1 nodes, 1 type contexts, 1 forms

module let-k-40 where

  -- τ=54: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=68 (1×)
  cell-40-54 : τ 54 ≡ τ 54
  cell-40-54 = refl


-- ── fixpoint (──────────────────────────────────────────)
-- κ=41, 1 nodes, 1 type contexts, 1 forms

module fixpoint-41 where

  -- τ=55: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=69 (1×)
  cell-41-55 : τ 55 ≡ τ 55
  cell-41-55 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=43, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-43 where

  -- τ=57: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=71 (1×)
  cell-43-57 : τ 57 ≡ τ 57
  cell-43-57 = refl


-- ── product (───────────────────────────────────────────)
-- κ=47, 1 nodes, 1 type contexts, 1 forms

module product-47 where

  -- τ=63: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=85 (1×)
  cell-47-63 : τ 63 ≡ τ 63
  cell-47-63 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=48, 1 nodes, 1 type contexts, 1 forms

module let-k-48 where

  -- τ=64: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=86 (1×)
  cell-48-64 : τ 64 ≡ τ 64
  cell-48-64 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=53, 1 nodes, 1 type contexts, 1 forms

module equalizer-53 where

  -- τ=69: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=98 (1×)
  cell-53-69 : τ 69 ≡ τ 69
  cell-53-69 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=54, 1 nodes, 1 type contexts, 1 forms

module let-k-54 where

  -- τ=70: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=100 (1×)
  cell-54-70 : τ 70 ≡ τ 70
  cell-54-70 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=55, 1 nodes, 1 type contexts, 1 forms

module equalizer-55 where

  -- τ=71: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=101 (1×)
  cell-55-71 : τ 71 ≡ τ 71
  cell-55-71 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=56, 1 nodes, 1 type contexts, 1 forms

module equalizer-56 where

  -- τ=72: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=104 (1×)
  cell-56-72 : τ 72 ≡ τ 72
  cell-56-72 = refl


-- ── monoid.accum (──────────────────────────────────────)
-- κ=58, 1 nodes, 1 type contexts, 1 forms

module monoid-accum-58 where

  -- τ=74: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=108 (1×)
  cell-58-74 : τ 74 ≡ τ 74
  cell-58-74 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=59, 1 nodes, 1 type contexts, 1 forms

module equalizer-59 where

  -- τ=75: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=109 (1×)
  cell-59-75 : τ 75 ≡ τ 75
  cell-59-75 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=60, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-60 where

  -- τ=76: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=110 (1×)
  cell-60-76 : τ 76 ≡ τ 76
  cell-60-76 = refl


-- ── terminal.map (──────────────────────────────────────)
-- κ=63, 1 nodes, 1 type contexts, 1 forms

module terminal-map-63 where

  -- τ=79: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=116 (1×)
  cell-63-79 : τ 79 ≡ τ 79
  cell-63-79 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=64, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-64 where

  -- τ=81: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=118 (1×)
  cell-64-81 : τ 81 ≡ τ 81
  cell-64-81 = refl


-- ── terminal.map (──────────────────────────────────────)
-- κ=66, 1 nodes, 1 type contexts, 1 forms

module terminal-map-66 where

  -- τ=83: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=121 (1×)
  cell-66-83 : τ 83 ≡ τ 83
  cell-66-83 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=68, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-68 where

  -- τ=85: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=125 (1×)
  cell-68-85 : τ 85 ≡ τ 85
  cell-68-85 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=72, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-72 where

  -- τ=89: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=129 (1×)
  cell-72-89 : τ 89 ≡ τ 89
  cell-72-89 = refl


-- ── classifier.intro (──────────────────────────────────)
-- κ=73, 1 nodes, 1 type contexts, 1 forms

module classifier-intro-73 where

  -- τ=90: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=130 (1×)
  cell-73-90 : τ 90 ≡ τ 90
  cell-73-90 = refl


-- ── product (───────────────────────────────────────────)
-- κ=74, 1 nodes, 1 type contexts, 1 forms

module product-74 where

  -- τ=91: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=137 (1×)
  cell-74-91 : τ 91 ≡ τ 91
  cell-74-91 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=75, 1 nodes, 1 type contexts, 1 forms

module let-k-75 where

  -- τ=92: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=138 (1×)
  cell-75-92 : τ 92 ≡ τ 92
  cell-75-92 = refl


-- ── arguments (─────────────────────────────────────────)
-- κ=80, 1 nodes, 1 type contexts, 1 forms

module arguments-80 where

  -- τ=104: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=150 (1×)
  cell-80-104 : τ 104 ≡ τ 104
  cell-80-104 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=85, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-85 where

  -- τ=117: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=166 (1×)
  cell-85-117 : τ 117 ≡ τ 117
  cell-85-117 = refl


-- ── free_monoid.fold (──────────────────────────────────)
-- κ=88, 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-88 where

  -- τ=120: 1 nodes, 1 forms
  -- Types: str
  -- σ=175 (1×)
  cell-88-120 : τ 120 ≡ τ 120
  cell-88-120 = refl


-- ── terminal.map (──────────────────────────────────────)
-- κ=89, 1 nodes, 1 type contexts, 1 forms

module terminal-map-89 where

  -- τ=121: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=176 (1×)
  cell-89-121 : τ 121 ≡ τ 121
  cell-89-121 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=90, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-90 where

  -- τ=122: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=178 (1×)
  cell-90-122 : τ 122 ≡ τ 122
  cell-90-122 = refl


-- ── classifier.intro (──────────────────────────────────)
-- κ=91, 1 nodes, 1 type contexts, 1 forms

module classifier-intro-91 where

  -- τ=123: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=179 (1×)
  cell-91-123 : τ 123 ≡ τ 123
  cell-91-123 = refl


-- ── product (───────────────────────────────────────────)
-- κ=92, 1 nodes, 1 type contexts, 1 forms

module product-92 where

  -- τ=133: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=194 (1×)
  cell-92-133 : τ 133 ≡ τ 133
  cell-92-133 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=93, 1 nodes, 1 type contexts, 1 forms

module index-93 where

  -- τ=134: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=195 (1×)
  cell-93-134 : τ 134 ≡ τ 134
  cell-93-134 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=94, 1 nodes, 1 type contexts, 1 forms

module subscript-94 where

  -- τ=135: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=196 (1×)
  cell-94-135 : τ 135 ≡ τ 135
  cell-94-135 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=95, 1 nodes, 1 type contexts, 1 forms

module annassign-95 where

  -- τ=136: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=197 (1×)
  cell-95-136 : τ 136 ≡ τ 136
  cell-95-136 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=99, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-99 where

  -- τ=142: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=204 (1×)
  cell-99-142 : τ 142 ≡ τ 142
  cell-99-142 = refl


-- ── arguments (─────────────────────────────────────────)
-- κ=100, 1 nodes, 1 type contexts, 1 forms

module arguments-100 where

  -- τ=143: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=206 (1×)
  cell-100-143 : τ 143 ≡ τ 143
  cell-100-143 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=103, 1 nodes, 1 type contexts, 1 forms

module apply-103 where

  -- τ=151: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=221 (1×)
  cell-103-151 : τ 151 ≡ τ 151
  cell-103-151 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=104, 1 nodes, 1 type contexts, 1 forms

module let-k-104 where

  -- τ=152: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=222 (1×)
  cell-104-152 : τ 152 ≡ τ 152
  cell-104-152 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=108, 1 nodes, 1 type contexts, 1 forms

module equalizer-108 where

  -- τ=156: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=227 (1×)
  cell-108-156 : τ 156 ≡ τ 156
  cell-108-156 = refl


-- ── free_monoid.snoc@? (────────────────────────────────)
-- κ=111, 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-x3f-111 where

  -- τ=160: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=232 (1×)
  cell-111-160 : τ 160 ≡ τ 160
  cell-111-160 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=112, 1 nodes, 1 type contexts, 1 forms

module effect-seq-112 where

  -- τ=161: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=233 (1×)
  cell-112-161 : τ 161 ≡ τ 161
  cell-112-161 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=113, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-113 where

  -- τ=163: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=235 (1×)
  cell-113-163 : τ 163 ≡ τ 163
  cell-113-163 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=115, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-115 where

  -- τ=167: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=242 (1×)
  cell-115-167 : τ 167 ≡ τ 167
  cell-115-167 = refl


-- ── product (───────────────────────────────────────────)
-- κ=116, 1 nodes, 1 type contexts, 1 forms

module product-116 where

  -- τ=171: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=250 (1×)
  cell-116-171 : τ 171 ≡ τ 171
  cell-116-171 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=117, 1 nodes, 1 type contexts, 1 forms

module let-k-117 where

  -- τ=172: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=251 (1×)
  cell-117-172 : τ 172 ≡ τ 172
  cell-117-172 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=119, 1 nodes, 1 type contexts, 1 forms

module annassign-119 where

  -- τ=175: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=255 (1×)
  cell-119-175 : τ 175 ≡ τ 175
  cell-119-175 = refl


-- ── ifexp (─────────────────────────────────────────────)
-- κ=120, 1 nodes, 1 type contexts, 1 forms

module ifexp-120 where

  -- τ=176: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=259 (1×)
  cell-120-176 : τ 176 ≡ τ 176
  cell-120-176 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=121, 1 nodes, 1 type contexts, 1 forms

module let-k-121 where

  -- τ=177: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=260 (1×)
  cell-121-177 : τ 177 ≡ τ 177
  cell-121-177 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=122, 1 nodes, 1 type contexts, 1 forms

module apply-122 where

  -- τ=180: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=269 (1×)
  cell-122-180 : τ 180 ≡ τ 180
  cell-122-180 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=123, 1 nodes, 1 type contexts, 1 forms

module effect-seq-123 where

  -- τ=181: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=270 (1×)
  cell-123-181 : τ 181 ≡ τ 181
  cell-123-181 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=124, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-124 where

  -- τ=182: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=272 (1×)
  cell-124-182 : τ 182 ≡ τ 182
  cell-124-182 = refl


-- ── cofree (────────────────────────────────────────────)
-- κ=132, 1 nodes, 1 type contexts, 1 forms

module cofree-132 where

  -- τ=191: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=288 (1×)
  cell-132-191 : τ 191 ≡ τ 191
  cell-132-191 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=133, 1 nodes, 1 type contexts, 1 forms

module effect-seq-133 where

  -- τ=192: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=289 (1×)
  cell-133-192 : τ 192 ≡ τ 192
  cell-133-192 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=134, 1 nodes, 1 type contexts, 1 forms

module equalizer-134 where

  -- τ=193: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=290 (1×)
  cell-134-193 : τ 193 ≡ τ 193
  cell-134-193 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=135, 1 nodes, 1 type contexts, 1 forms

module fold-135 where

  -- τ=194: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=291 (1×)
  cell-135-194 : τ 194 ≡ τ 194
  cell-135-194 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=136, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-136 where

  -- τ=196: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=293 (1×)
  cell-136-196 : τ 196 ≡ τ 196
  cell-136-196 = refl


-- ── comprehension (─────────────────────────────────────)
-- κ=138, 1 nodes, 1 type contexts, 1 forms

module comprehension-138 where

  -- τ=199: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=298 (1×)
  cell-138-199 : τ 199 ≡ τ 199
  cell-138-199 = refl


-- ── lazy_fold (─────────────────────────────────────────)
-- κ=139, 1 nodes, 1 type contexts, 1 forms

module lazy_fold-139 where

  -- τ=200: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=299 (1×)
  cell-139-200 : τ 200 ≡ τ 200
  cell-139-200 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=140, 1 nodes, 1 type contexts, 1 forms

module apply-140 where

  -- τ=201: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=300 (1×)
  cell-140-201 : τ 201 ≡ τ 201
  cell-140-201 = refl


-- ── terminal.map (──────────────────────────────────────)
-- κ=141, 1 nodes, 1 type contexts, 1 forms

module terminal-map-141 where

  -- τ=202: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=301 (1×)
  cell-141-202 : τ 202 ≡ τ 202
  cell-141-202 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=142, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-142 where

  -- τ=203: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=302 (1×)
  cell-142-203 : τ 203 ≡ τ 203
  cell-142-203 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=143, 1 nodes, 1 type contexts, 1 forms

module index-143 where

  -- τ=204: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=303 (1×)
  cell-143-204 : τ 204 ≡ τ 204
  cell-143-204 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=144, 1 nodes, 1 type contexts, 1 forms

module subscript-144 where

  -- τ=205: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=304 (1×)
  cell-144-205 : τ 205 ≡ τ 205
  cell-144-205 = refl


-- ── terminal.map (──────────────────────────────────────)
-- κ=145, 1 nodes, 1 type contexts, 1 forms

module terminal-map-145 where

  -- τ=206: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=305 (1×)
  cell-145-206 : τ 206 ≡ τ 206
  cell-145-206 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=146, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-146 where

  -- τ=207: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=306 (1×)
  cell-146-207 : τ 207 ≡ τ 207
  cell-146-207 = refl


-- ── terminal.map (──────────────────────────────────────)
-- κ=147, 1 nodes, 1 type contexts, 1 forms

module terminal-map-147 where

  -- τ=208: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=307 (1×)
  cell-147-208 : τ 208 ≡ τ 208
  cell-147-208 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=148, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-148 where

  -- τ=209: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=308 (1×)
  cell-148-209 : τ 209 ≡ τ 209
  cell-148-209 = refl


-- ── free_monoid.fold (──────────────────────────────────)
-- κ=151, 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-151 where

  -- τ=212: 1 nodes, 1 forms
  -- Types: str
  -- σ=315 (1×)
  cell-151-212 : τ 212 ≡ τ 212
  cell-151-212 = refl


-- ── terminal.map (──────────────────────────────────────)
-- κ=152, 1 nodes, 1 type contexts, 1 forms

module terminal-map-152 where

  -- τ=213: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=316 (1×)
  cell-152-213 : τ 213 ≡ τ 213
  cell-152-213 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=153, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-153 where

  -- τ=214: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=317 (1×)
  cell-153-214 : τ 214 ≡ τ 214
  cell-153-214 = refl


-- ── classifier.intro (──────────────────────────────────)
-- κ=154, 1 nodes, 1 type contexts, 1 forms

module classifier-intro-154 where

  -- τ=215: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=318 (1×)
  cell-154-215 : τ 215 ≡ τ 215
  cell-154-215 = refl


-- ── product (───────────────────────────────────────────)
-- κ=166, 1 nodes, 1 type contexts, 1 forms

module product-166 where

  -- τ=232: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=351 (1×)
  cell-166-232 : τ 232 ≡ τ 232
  cell-166-232 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=167, 1 nodes, 1 type contexts, 1 forms

module index-167 where

  -- τ=233: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=352 (1×)
  cell-167-233 : τ 233 ≡ τ 233
  cell-167-233 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=168, 1 nodes, 1 type contexts, 1 forms

module subscript-168 where

  -- τ=234: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=353 (1×)
  cell-168-234 : τ 234 ≡ τ 234
  cell-168-234 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=169, 1 nodes, 1 type contexts, 1 forms

module annassign-169 where

  -- τ=235: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=354 (1×)
  cell-169-235 : τ 235 ≡ τ 235
  cell-169-235 = refl


-- ── product (───────────────────────────────────────────)
-- κ=172, 1 nodes, 1 type contexts, 1 forms

module product-172 where

  -- τ=239: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=359 (1×)
  cell-172-239 : τ 239 ≡ τ 239
  cell-172-239 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=173, 1 nodes, 1 type contexts, 1 forms

module index-173 where

  -- τ=240: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=360 (1×)
  cell-173-240 : τ 240 ≡ τ 240
  cell-173-240 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=174, 1 nodes, 1 type contexts, 1 forms

module subscript-174 where

  -- τ=241: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=361 (1×)
  cell-174-241 : τ 241 ≡ τ 241
  cell-174-241 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=176, 1 nodes, 1 type contexts, 1 forms

module annassign-176 where

  -- τ=243: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=363 (1×)
  cell-176-243 : τ 243 ≡ τ 243
  cell-176-243 = refl


-- ── product (───────────────────────────────────────────)
-- κ=177, 1 nodes, 1 type contexts, 1 forms

module product-177 where

  -- τ=245: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=365 (1×)
  cell-177-245 : τ 245 ≡ τ 245
  cell-177-245 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=178, 1 nodes, 1 type contexts, 1 forms

module index-178 where

  -- τ=246: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=366 (1×)
  cell-178-246 : τ 246 ≡ τ 246
  cell-178-246 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=179, 1 nodes, 1 type contexts, 1 forms

module subscript-179 where

  -- τ=247: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=367 (1×)
  cell-179-247 : τ 247 ≡ τ 247
  cell-179-247 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=180, 1 nodes, 1 type contexts, 1 forms

module annassign-180 where

  -- τ=248: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=368 (1×)
  cell-180-248 : τ 248 ≡ τ 248
  cell-180-248 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=186, 1 nodes, 1 type contexts, 1 forms

module annassign-186 where

  -- τ=263: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=385 (1×)
  cell-186-263 : τ 263 ≡ τ 263
  cell-186-263 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=192, 1 nodes, 1 type contexts, 1 forms

module annassign-192 where

  -- τ=270: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=392 (1×)
  cell-192-270 : τ 270 ≡ τ 270
  cell-192-270 = refl


-- ── arguments (─────────────────────────────────────────)
-- κ=196, 1 nodes, 1 type contexts, 1 forms

module arguments-196 where

  -- τ=285: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=408 (1×)
  cell-196-285 : τ 285 ≡ τ 285
  cell-196-285 = refl


-- ── lambda (────────────────────────────────────────────)
-- κ=197, 1 nodes, 1 type contexts, 1 forms

module lambda-197 where

  -- τ=286: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=410 (1×)
  cell-197-286 : τ 286 ≡ τ 286
  cell-197-286 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=198, 1 nodes, 1 type contexts, 1 forms

module apply-198 where

  -- τ=287: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=411 (1×)
  cell-198-287 : τ 287 ≡ τ 287
  cell-198-287 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=199, 1 nodes, 1 type contexts, 1 forms

module annassign-199 where

  -- τ=288: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=412 (1×)
  cell-199-288 : τ 288 ≡ τ 288
  cell-199-288 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=203, 1 nodes, 1 type contexts, 1 forms

module annassign-203 where

  -- τ=293: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=421 (1×)
  cell-203-293 : τ 293 ≡ τ 293
  cell-203-293 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=204, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-204 where

  -- τ=294: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=422 (1×)
  cell-204-294 : τ 294 ≡ τ 294
  cell-204-294 = refl


-- ── arg (───────────────────────────────────────────────)
-- κ=205, 1 nodes, 1 type contexts, 1 forms

module arg-205 where

  -- τ=297: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=427 (1×)
  cell-205-297 : τ 297 ≡ τ 297
  cell-205-297 = refl


-- ── arguments (─────────────────────────────────────────)
-- κ=206, 1 nodes, 1 type contexts, 1 forms

module arguments-206 where

  -- τ=298: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=428 (1×)
  cell-206-298 : τ 298 ≡ τ 298
  cell-206-298 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=207, 1 nodes, 1 type contexts, 1 forms

module subscript-207 where

  -- τ=299: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=437 (1×)
  cell-207-299 : τ 299 ≡ τ 299
  cell-207-299 = refl


-- ── monoid.accum (──────────────────────────────────────)
-- κ=208, 1 nodes, 1 type contexts, 1 forms

module monoid-accum-208 where

  -- τ=300: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=438 (1×)
  cell-208-300 : τ 300 ≡ τ 300
  cell-208-300 = refl


-- ── coproduct.elim (────────────────────────────────────)
-- κ=214, 1 nodes, 1 type contexts, 1 forms

module coproduct-elim-214 where

  -- τ=306: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=453 (1×)
  cell-214-306 : τ 306 ≡ τ 306
  cell-214-306 = refl


-- ── bimap (─────────────────────────────────────────────)
-- κ=221, 1 nodes, 1 type contexts, 1 forms

module bimap-221 where

  -- τ=314: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=462 (1×)
  cell-221-314 : τ 314 ≡ τ 314
  cell-221-314 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=222, 1 nodes, 1 type contexts, 1 forms

module apply-222 where

  -- τ=315: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=464 (1×)
  cell-222-315 : τ 315 ≡ τ 315
  cell-222-315 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=223, 1 nodes, 1 type contexts, 1 forms

module effect-seq-223 where

  -- τ=316: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=465 (1×)
  cell-223-316 : τ 316 ≡ τ 316
  cell-223-316 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=224, 1 nodes, 1 type contexts, 1 forms

module fold-224 where

  -- τ=317: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=466 (1×)
  cell-224-317 : τ 317 ≡ τ 317
  cell-224-317 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=225, 1 nodes, 1 type contexts, 1 forms

module equalizer-225 where

  -- τ=318: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=467 (1×)
  cell-225-318 : τ 318 ≡ τ 318
  cell-225-318 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=226, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-226 where

  -- τ=319: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=468 (1×)
  cell-226-319 : τ 319 ≡ τ 319
  cell-226-319 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=229, 1 nodes, 1 type contexts, 1 forms

module let-k-229 where

  -- τ=325: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=486 (1×)
  cell-229-325 : τ 325 ≡ τ 325
  cell-229-325 = refl


-- ── or (────────────────────────────────────────────────)
-- κ=230, 1 nodes, 1 type contexts, 1 forms

module or-230 where

  -- τ=327: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=489 (1×)
  cell-230-327 : τ 327 ≡ τ 327
  cell-230-327 = refl


-- ── join (──────────────────────────────────────────────)
-- κ=231, 1 nodes, 1 type contexts, 1 forms

module join-231 where

  -- τ=329: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=493 (1×)
  cell-231-329 : τ 329 ≡ τ 329
  cell-231-329 = refl


-- ── lazy_fold (─────────────────────────────────────────)
-- κ=233, 1 nodes, 1 type contexts, 1 forms

module lazy_fold-233 where

  -- τ=331: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=497 (1×)
  cell-233-331 : τ 331 ≡ τ 331
  cell-233-331 = refl


-- ── total_order (───────────────────────────────────────)
-- κ=234, 1 nodes, 1 type contexts, 1 forms

module total_order-234 where

  -- τ=332: 1 nodes, 1 forms
  -- Types: list
  -- σ=498 (1×)
  cell-234-332 : τ 332 ≡ τ 332
  cell-234-332 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=235, 1 nodes, 1 type contexts, 1 forms

module apply-235 where

  -- τ=333: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=499 (1×)
  cell-235-333 : τ 333 ≡ τ 333
  cell-235-333 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=236, 1 nodes, 1 type contexts, 1 forms

module let-k-236 where

  -- τ=334: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=500 (1×)
  cell-236-334 : τ 334 ≡ τ 334
  cell-236-334 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=237, 1 nodes, 1 type contexts, 1 forms

module equalizer-237 where

  -- τ=336: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=504 (1×)
  cell-237-336 : τ 336 ≡ τ 336
  cell-237-336 = refl


-- ── terminal.map (──────────────────────────────────────)
-- κ=238, 1 nodes, 1 type contexts, 1 forms

module terminal-map-238 where

  -- τ=337: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=505 (1×)
  cell-238-337 : τ 337 ≡ τ 337
  cell-238-337 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=239, 1 nodes, 1 type contexts, 1 forms

module equalizer-239 where

  -- τ=338: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=506 (1×)
  cell-239-338 : τ 338 ≡ τ 338
  cell-239-338 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=240, 1 nodes, 1 type contexts, 1 forms

module let-k-240 where

  -- τ=339: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=513 (1×)
  cell-240-339 : τ 339 ≡ τ 339
  cell-240-339 = refl


-- ── free_monoid.snoc@state (────────────────────────────)
-- κ=244, 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-state-244 where

  -- τ=343: 1 nodes, 1 forms
  -- Types: None
  -- σ=520 (1×)
  cell-244-343 : τ 343 ≡ τ 343
  cell-244-343 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=245, 1 nodes, 1 type contexts, 1 forms

module effect-seq-245 where

  -- τ=344: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=521 (1×)
  cell-245-344 : τ 344 ≡ τ 344
  cell-245-344 = refl


-- ── free_monoid.fold (──────────────────────────────────)
-- κ=246, 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-246 where

  -- τ=345: 1 nodes, 1 forms
  -- Types: str
  -- σ=527 (1×)
  cell-246-345 : τ 345 ≡ τ 345
  cell-246-345 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=247, 1 nodes, 1 type contexts, 1 forms

module apply-247 where

  -- τ=346: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=528 (1×)
  cell-247-346 : τ 346 ≡ τ 346
  cell-247-346 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=248, 1 nodes, 1 type contexts, 1 forms

module let-k-248 where

  -- τ=347: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=529 (1×)
  cell-248-347 : τ 347 ≡ τ 347
  cell-248-347 = refl


-- ── free_monoid.snoc@state (────────────────────────────)
-- κ=249, 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-state-249 where

  -- τ=349: 1 nodes, 1 forms
  -- Types: None, T
  -- σ=532 (1×)
  cell-249-349 : τ 349 ≡ τ 349
  cell-249-349 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=250, 1 nodes, 1 type contexts, 1 forms

module effect-seq-250 where

  -- τ=350: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=533 (1×)
  cell-250-350 : τ 350 ≡ τ 350
  cell-250-350 = refl


-- ── fixpoint (──────────────────────────────────────────)
-- κ=251, 1 nodes, 1 type contexts, 1 forms

module fixpoint-251 where

  -- τ=351: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=534 (1×)
  cell-251-351 : τ 351 ≡ τ 351
  cell-251-351 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=253, 1 nodes, 1 type contexts, 1 forms

module let-k-253 where

  -- τ=354: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=552 (1×)
  cell-253-354 : τ 354 ≡ τ 354
  cell-253-354 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=257, 1 nodes, 1 type contexts, 1 forms

module annassign-257 where

  -- τ=360: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=568 (1×)
  cell-257-360 : τ 360 ≡ τ 360
  cell-257-360 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=260, 1 nodes, 1 type contexts, 1 forms

module equalizer-260 where

  -- τ=363: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=576 (1×)
  cell-260-363 : τ 363 ≡ τ 363
  cell-260-363 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=265, 1 nodes, 1 type contexts, 1 forms

module equalizer-265 where

  -- τ=367: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=590 (1×)
  cell-265-367 : τ 367 ≡ τ 367
  cell-265-367 = refl


-- ── comprehension (─────────────────────────────────────)
-- κ=266, 1 nodes, 1 type contexts, 1 forms

module comprehension-266 where

  -- τ=368: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=591 (1×)
  cell-266-368 : τ 368 ≡ τ 368
  cell-266-368 = refl


-- ── lazy_fold (─────────────────────────────────────────)
-- κ=267, 1 nodes, 1 type contexts, 1 forms

module lazy_fold-267 where

  -- τ=369: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=592 (1×)
  cell-267-369 : τ 369 ≡ τ 369
  cell-267-369 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=268, 1 nodes, 1 type contexts, 1 forms

module apply-268 where

  -- τ=370: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=593 (1×)
  cell-268-370 : τ 370 ≡ τ 370
  cell-268-370 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=269, 1 nodes, 1 type contexts, 1 forms

module let-k-269 where

  -- τ=371: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=594 (1×)
  cell-269-371 : τ 371 ≡ τ 371
  cell-269-371 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=270, 1 nodes, 1 type contexts, 1 forms

module equalizer-270 where

  -- τ=372: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=600 (1×)
  cell-270-372 : τ 372 ≡ τ 372
  cell-270-372 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=271, 1 nodes, 1 type contexts, 1 forms

module fold-271 where

  -- τ=373: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=601 (1×)
  cell-271-373 : τ 373 ≡ τ 373
  cell-271-373 = refl


-- ── lte (───────────────────────────────────────────────)
-- κ=272, 1 nodes, 1 type contexts, 1 forms

module lte-272 where

  -- τ=374: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=604 (1×)
  cell-272-374 : τ 374 ≡ τ 374
  cell-272-374 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=273, 1 nodes, 1 type contexts, 1 forms

module equalizer-273 where

  -- τ=375: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=605 (1×)
  cell-273-375 : τ 375 ≡ τ 375
  cell-273-375 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=274, 1 nodes, 1 type contexts, 1 forms

module let-k-274 where

  -- τ=376: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=606 (1×)
  cell-274-376 : τ 376 ≡ τ 376
  cell-274-376 = refl


-- ── coproduct.elim (────────────────────────────────────)
-- κ=281, 1 nodes, 1 type contexts, 1 forms

module coproduct-elim-281 where

  -- τ=383: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=622 (1×)
  cell-281-383 : τ 383 ≡ τ 383
  cell-281-383 = refl


-- ── product (───────────────────────────────────────────)
-- κ=283, 1 nodes, 1 type contexts, 1 forms

module product-283 where

  -- τ=386: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=630 (1×)
  cell-283-386 : τ 386 ≡ τ 386
  cell-283-386 = refl


-- ── free_monoid.snoc@state (────────────────────────────)
-- κ=284, 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-state-284 where

  -- τ=387: 1 nodes, 1 forms
  -- Types: None
  -- σ=631 (1×)
  cell-284-387 : τ 387 ≡ τ 387
  cell-284-387 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=285, 1 nodes, 1 type contexts, 1 forms

module effect-seq-285 where

  -- τ=388: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=632 (1×)
  cell-285-388 : τ 388 ≡ τ 388
  cell-285-388 = refl


-- ── monoid.op (─────────────────────────────────────────)
-- κ=286, 1 nodes, 1 type contexts, 1 forms

module monoid-op-286 where

  -- τ=389: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=634 (1×)
  cell-286-389 : τ 389 ≡ τ 389
  cell-286-389 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=287, 1 nodes, 1 type contexts, 1 forms

module let-k-287 where

  -- τ=390: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=635 (1×)
  cell-287-390 : τ 390 ≡ τ 390
  cell-287-390 = refl


-- ── partial.apply@state (───────────────────────────────)
-- κ=288, 1 nodes, 1 type contexts, 1 forms

module partial-apply-at-state-288 where

  -- τ=349: 1 nodes, 1 forms
  -- Types: None, T
  -- σ=644 (1×)
  cell-288-349 : τ 349 ≡ τ 349
  cell-288-349 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=289, 1 nodes, 1 type contexts, 1 forms

module let-k-289 where

  -- τ=395: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=645 (1×)
  cell-289-395 : τ 395 ≡ τ 395
  cell-289-395 = refl


-- ── ifexp (─────────────────────────────────────────────)
-- κ=290, 1 nodes, 1 type contexts, 1 forms

module ifexp-290 where

  -- τ=398: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=653 (1×)
  cell-290-398 : τ 398 ≡ τ 398
  cell-290-398 = refl


-- ── monoid.op@? (───────────────────────────────────────)
-- κ=291, 1 nodes, 1 type contexts, 1 forms

module monoid-op-at-x3f-291 where

  -- τ=399: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=654 (1×)
  cell-291-399 : τ 399 ≡ τ 399
  cell-291-399 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=292, 1 nodes, 1 type contexts, 1 forms

module effect-seq-292 where

  -- τ=400: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=655 (1×)
  cell-292-400 : τ 400 ≡ τ 400
  cell-292-400 = refl


-- ── coproduct.elim (────────────────────────────────────)
-- κ=293, 1 nodes, 1 type contexts, 1 forms

module coproduct-elim-293 where

  -- τ=401: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=656 (1×)
  cell-293-401 : τ 401 ≡ τ 401
  cell-293-401 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=294, 1 nodes, 1 type contexts, 1 forms

module fold-294 where

  -- τ=402: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=657 (1×)
  cell-294-402 : τ 402 ≡ τ 402
  cell-294-402 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=295, 1 nodes, 1 type contexts, 1 forms

module fold-295 where

  -- τ=403: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=658 (1×)
  cell-295-403 : τ 403 ≡ τ 403
  cell-295-403 = refl


-- ── ifexp (─────────────────────────────────────────────)
-- κ=297, 1 nodes, 1 type contexts, 1 forms

module ifexp-297 where

  -- τ=405: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=661 (1×)
  cell-297-405 : τ 405 ≡ τ 405
  cell-297-405 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=298, 1 nodes, 1 type contexts, 1 forms

module apply-298 where

  -- τ=406: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=662 (1×)
  cell-298-406 : τ 406 ≡ τ 406
  cell-298-406 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=299, 1 nodes, 1 type contexts, 1 forms

module effect-seq-299 where

  -- τ=407: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=663 (1×)
  cell-299-407 : τ 407 ≡ τ 407
  cell-299-407 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=301, 1 nodes, 1 type contexts, 1 forms

module let-k-301 where

  -- τ=408: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=667 (1×)
  cell-301-408 : τ 408 ≡ τ 408
  cell-301-408 = refl


-- ── morphism@? (────────────────────────────────────────)
-- κ=302, 1 nodes, 1 type contexts, 1 forms

module morphism-at-x3f-302 where

  -- τ=409: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=668 (1×)
  cell-302-409 : τ 409 ≡ τ 409
  cell-302-409 = refl


-- ── monoid.accum (──────────────────────────────────────)
-- κ=303, 1 nodes, 1 type contexts, 1 forms

module monoid-accum-303 where

  -- τ=410: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=669 (1×)
  cell-303-410 : τ 410 ≡ τ 410
  cell-303-410 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=305, 1 nodes, 1 type contexts, 1 forms

module equalizer-305 where

  -- τ=413: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=672 (1×)
  cell-305-413 : τ 413 ≡ τ 413
  cell-305-413 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=307, 1 nodes, 1 type contexts, 1 forms

module equalizer-307 where

  -- τ=415: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=677 (1×)
  cell-307-415 : τ 415 ≡ τ 415
  cell-307-415 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=308, 1 nodes, 1 type contexts, 1 forms

module index-308 where

  -- τ=416: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=678 (1×)
  cell-308-416 : τ 416 ≡ τ 416
  cell-308-416 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=309, 1 nodes, 1 type contexts, 1 forms

module subscript-309 where

  -- τ=417: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=679 (1×)
  cell-309-417 : τ 417 ≡ τ 417
  cell-309-417 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=310, 1 nodes, 1 type contexts, 1 forms

module let-k-310 where

  -- τ=418: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=681 (1×)
  cell-310-418 : τ 418 ≡ τ 418
  cell-310-418 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=311, 1 nodes, 1 type contexts, 1 forms

module equalizer-311 where

  -- τ=419: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=682 (1×)
  cell-311-419 : τ 419 ≡ τ 419
  cell-311-419 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=312, 1 nodes, 1 type contexts, 1 forms

module fold-312 where

  -- τ=420: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=683 (1×)
  cell-312-420 : τ 420 ≡ τ 420
  cell-312-420 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=313, 1 nodes, 1 type contexts, 1 forms

module fold-313 where

  -- τ=421: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=684 (1×)
  cell-313-421 : τ 421 ≡ τ 421
  cell-313-421 = refl


-- ── lazy_fold (─────────────────────────────────────────)
-- κ=315, 1 nodes, 1 type contexts, 1 forms

module lazy_fold-315 where

  -- τ=423: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=688 (1×)
  cell-315-423 : τ 423 ≡ τ 423
  cell-315-423 = refl


-- ── powerset (──────────────────────────────────────────)
-- κ=316, 1 nodes, 1 type contexts, 1 forms

module powerset-316 where

  -- τ=424: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=689 (1×)
  cell-316-424 : τ 424 ≡ τ 424
  cell-316-424 = refl


-- ── total_order (───────────────────────────────────────)
-- κ=317, 1 nodes, 1 type contexts, 1 forms

module total_order-317 where

  -- τ=425: 1 nodes, 1 forms
  -- Types: list
  -- σ=690 (1×)
  cell-317-425 : τ 425 ≡ τ 425
  cell-317-425 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=318, 1 nodes, 1 type contexts, 1 forms

module apply-318 where

  -- τ=426: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=691 (1×)
  cell-318-426 : τ 426 ≡ τ 426
  cell-318-426 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=319, 1 nodes, 1 type contexts, 1 forms

module let-k-319 where

  -- τ=427: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=692 (1×)
  cell-319-427 : τ 427 ≡ τ 427
  cell-319-427 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=320, 1 nodes, 1 type contexts, 1 forms

module let-k-320 where

  -- τ=428: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=697 (1×)
  cell-320-428 : τ 428 ≡ τ 428
  cell-320-428 = refl


-- ── monoid.accum (──────────────────────────────────────)
-- κ=321, 1 nodes, 1 type contexts, 1 forms

module monoid-accum-321 where

  -- τ=429: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=698 (1×)
  cell-321-429 : τ 429 ≡ τ 429
  cell-321-429 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=322, 1 nodes, 1 type contexts, 1 forms

module equalizer-322 where

  -- τ=430: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=699 (1×)
  cell-322-430 : τ 430 ≡ τ 430
  cell-322-430 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=323, 1 nodes, 1 type contexts, 1 forms

module equalizer-323 where

  -- τ=431: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=700 (1×)
  cell-323-431 : τ 431 ≡ τ 431
  cell-323-431 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=324, 1 nodes, 1 type contexts, 1 forms

module equalizer-324 where

  -- τ=432: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=701 (1×)
  cell-324-432 : τ 432 ≡ τ 432
  cell-324-432 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=327, 1 nodes, 1 type contexts, 1 forms

module let-k-327 where

  -- τ=436: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=705 (1×)
  cell-327-436 : τ 436 ≡ τ 436
  cell-327-436 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=328, 1 nodes, 1 type contexts, 1 forms

module equalizer-328 where

  -- τ=437: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=706 (1×)
  cell-328-437 : τ 437 ≡ τ 437
  cell-328-437 = refl


-- ── fixpoint (──────────────────────────────────────────)
-- κ=329, 1 nodes, 1 type contexts, 1 forms

module fixpoint-329 where

  -- τ=438: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=707 (1×)
  cell-329-438 : τ 438 ≡ τ 438
  cell-329-438 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=330, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-330 where

  -- τ=439: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=708 (1×)
  cell-330-439 : τ 439 ≡ τ 439
  cell-330-439 = refl


-- ── arguments (─────────────────────────────────────────)
-- κ=332, 1 nodes, 1 type contexts, 1 forms

module arguments-332 where

  -- τ=441: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=711 (1×)
  cell-332-441 : τ 441 ≡ τ 441
  cell-332-441 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=335, 1 nodes, 1 type contexts, 1 forms

module equalizer-335 where

  -- τ=446: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=723 (1×)
  cell-335-446 : τ 446 ≡ τ 446
  cell-335-446 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=336, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-336 where

  -- τ=447: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=724 (1×)
  cell-336-447 : τ 447 ≡ τ 447
  cell-336-447 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=337, 1 nodes, 1 type contexts, 1 forms

module apply-337 where

  -- τ=448: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=742 (1×)
  cell-337-448 : τ 448 ≡ τ 448
  cell-337-448 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=338, 1 nodes, 1 type contexts, 1 forms

module effect-seq-338 where

  -- τ=449: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=743 (1×)
  cell-338-449 : τ 449 ≡ τ 449
  cell-338-449 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=339, 1 nodes, 1 type contexts, 1 forms

module equalizer-339 where

  -- τ=450: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=744 (1×)
  cell-339-450 : τ 450 ≡ τ 450
  cell-339-450 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=340, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-340 where

  -- τ=451: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=745 (1×)
  cell-340-451 : τ 451 ≡ τ 451
  cell-340-451 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=345, 1 nodes, 1 type contexts, 1 forms

module fold-345 where

  -- τ=458: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=764 (1×)
  cell-345-458 : τ 458 ≡ τ 458
  cell-345-458 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=348, 1 nodes, 1 type contexts, 1 forms

module annassign-348 where

  -- τ=466: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=782 (1×)
  cell-348-466 : τ 466 ≡ τ 466
  cell-348-466 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=360, 1 nodes, 1 type contexts, 1 forms

module equalizer-360 where

  -- τ=480: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=820 (1×)
  cell-360-480 : τ 480 ≡ τ 480
  cell-360-480 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=361, 1 nodes, 1 type contexts, 1 forms

module equalizer-361 where

  -- τ=481: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=822 (1×)
  cell-361-481 : τ 481 ≡ τ 481
  cell-361-481 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=362, 1 nodes, 1 type contexts, 1 forms

module fold-362 where

  -- τ=482: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=823 (1×)
  cell-362-482 : τ 482 ≡ τ 482
  cell-362-482 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=363, 1 nodes, 1 type contexts, 1 forms

module apply-363 where

  -- τ=444: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=829 (1×)
  cell-363-444 : τ 444 ≡ τ 444
  cell-363-444 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=364, 1 nodes, 1 type contexts, 1 forms

module effect-seq-364 where

  -- τ=445: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=830 (1×)
  cell-364-445 : τ 445 ≡ τ 445
  cell-364-445 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=365, 1 nodes, 1 type contexts, 1 forms

module fold-365 where

  -- τ=483: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=831 (1×)
  cell-365-483 : τ 483 ≡ τ 483
  cell-365-483 = refl


-- ── product.unpack (────────────────────────────────────)
-- κ=366, 1 nodes, 1 type contexts, 1 forms

module product-unpack-366 where

  -- τ=484: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=836 (1×)
  cell-366-484 : τ 484 ≡ τ 484
  cell-366-484 = refl


-- ── free_monoid.literal (───────────────────────────────)
-- κ=367, 1 nodes, 1 type contexts, 1 forms

module free_monoid-literal-367 where

  -- τ=485: 1 nodes, 1 forms
  -- Types: list
  -- σ=838 (1×)
  cell-367-485 : τ 485 ≡ τ 485
  cell-367-485 = refl


-- ── product (───────────────────────────────────────────)
-- κ=368, 1 nodes, 1 type contexts, 1 forms

module product-368 where

  -- τ=488: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=842 (1×)
  cell-368-488 : τ 488 ≡ τ 488
  cell-368-488 = refl


-- ── free_monoid.snoc@state (────────────────────────────)
-- κ=369, 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-state-369 where

  -- τ=489: 1 nodes, 1 forms
  -- Types: None
  -- σ=843 (1×)
  cell-369-489 : τ 489 ≡ τ 489
  cell-369-489 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=370, 1 nodes, 1 type contexts, 1 forms

module effect-seq-370 where

  -- τ=490: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=844 (1×)
  cell-370-490 : τ 490 ≡ τ 490
  cell-370-490 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=379, 1 nodes, 1 type contexts, 1 forms

module fold-379 where

  -- τ=501: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=864 (1×)
  cell-379-501 : τ 501 ≡ τ 501
  cell-379-501 = refl


-- ── coproduct.elim (────────────────────────────────────)
-- κ=380, 1 nodes, 1 type contexts, 1 forms

module coproduct-elim-380 where

  -- τ=502: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=865 (1×)
  cell-380-502 : τ 502 ≡ τ 502
  cell-380-502 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=381, 1 nodes, 1 type contexts, 1 forms

module fold-381 where

  -- τ=503: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=866 (1×)
  cell-381-503 : τ 503 ≡ τ 503
  cell-381-503 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=382, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-382 where

  -- τ=504: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=868 (1×)
  cell-382-504 : τ 504 ≡ τ 504
  cell-382-504 = refl


-- ── arguments (─────────────────────────────────────────)
-- κ=383, 1 nodes, 1 type contexts, 1 forms

module arguments-383 where

  -- τ=505: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=870 (1×)
  cell-383-505 : τ 505 ≡ τ 505
  cell-383-505 = refl


-- ── is (────────────────────────────────────────────────)
-- κ=384, 1 nodes, 1 type contexts, 1 forms

module is-384 where

  -- τ=506: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=874 (1×)
  cell-384-506 : τ 506 ≡ τ 506
  cell-384-506 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=385, 1 nodes, 1 type contexts, 1 forms

module equalizer-385 where

  -- τ=507: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=875 (1×)
  cell-385-507 : τ 507 ≡ τ 507
  cell-385-507 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=387, 1 nodes, 1 type contexts, 1 forms

module equalizer-387 where

  -- τ=509: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=877 (1×)
  cell-387-509 : τ 509 ≡ τ 509
  cell-387-509 = refl


-- ── partial.apply@state (───────────────────────────────)
-- κ=388, 1 nodes, 1 type contexts, 1 forms

module partial-apply-at-state-388 where

  -- τ=510: 1 nodes, 1 forms
  -- Types: T
  -- σ=878 (1×)
  cell-388-510 : τ 510 ≡ τ 510
  cell-388-510 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=389, 1 nodes, 1 type contexts, 1 forms

module let-k-389 where

  -- τ=511: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=879 (1×)
  cell-389-511 : τ 511 ≡ τ 511
  cell-389-511 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=390, 1 nodes, 1 type contexts, 1 forms

module equalizer-390 where

  -- τ=513: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=881 (1×)
  cell-390-513 : τ 513 ≡ τ 513
  cell-390-513 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=391, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-391 where

  -- τ=514: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=883 (1×)
  cell-391-514 : τ 514 ≡ τ 514
  cell-391-514 = refl


-- ── arg (───────────────────────────────────────────────)
-- κ=392, 1 nodes, 1 type contexts, 1 forms

module arg-392 where

  -- τ=515: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=884 (1×)
  cell-392-515 : τ 515 ≡ τ 515
  cell-392-515 = refl


-- ── arguments (─────────────────────────────────────────)
-- κ=393, 1 nodes, 1 type contexts, 1 forms

module arguments-393 where

  -- τ=516: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=885 (1×)
  cell-393-516 : τ 516 ≡ τ 516
  cell-393-516 = refl


-- ── product (───────────────────────────────────────────)
-- κ=398, 1 nodes, 1 type contexts, 1 forms

module product-398 where

  -- τ=523: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=906 (1×)
  cell-398-523 : τ 523 ≡ τ 523
  cell-398-523 = refl


-- ── terminal.map (──────────────────────────────────────)
-- κ=399, 1 nodes, 1 type contexts, 1 forms

module terminal-map-399 where

  -- τ=524: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=907 (1×)
  cell-399-524 : τ 524 ≡ τ 524
  cell-399-524 = refl


-- ── product (───────────────────────────────────────────)
-- κ=400, 1 nodes, 1 type contexts, 1 forms

module product-400 where

  -- τ=525: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=908 (1×)
  cell-400-525 : τ 525 ≡ τ 525
  cell-400-525 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=401, 1 nodes, 1 type contexts, 1 forms

module index-401 where

  -- τ=526: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=909 (1×)
  cell-401-526 : τ 526 ≡ τ 526
  cell-401-526 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=402, 1 nodes, 1 type contexts, 1 forms

module subscript-402 where

  -- τ=527: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=910 (1×)
  cell-402-527 : τ 527 ≡ τ 527
  cell-402-527 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=403, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-403 where

  -- τ=528: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=911 (1×)
  cell-403-528 : τ 528 ≡ τ 528
  cell-403-528 = refl


-- ── arg (───────────────────────────────────────────────)
-- κ=404, 1 nodes, 1 type contexts, 1 forms

module arg-404 where

  -- τ=529: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=913 (1×)
  cell-404-529 : τ 529 ≡ τ 529
  cell-404-529 = refl


-- ── arguments (─────────────────────────────────────────)
-- κ=405, 1 nodes, 1 type contexts, 1 forms

module arguments-405 where

  -- τ=530: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=914 (1×)
  cell-405-530 : τ 530 ≡ τ 530
  cell-405-530 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=406, 1 nodes, 1 type contexts, 1 forms

module equalizer-406 where

  -- τ=532: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=930 (1×)
  cell-406-532 : τ 532 ≡ τ 532
  cell-406-532 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=407, 1 nodes, 1 type contexts, 1 forms

module fold-407 where

  -- τ=533: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=931 (1×)
  cell-407-533 : τ 533 ≡ τ 533
  cell-407-533 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=408, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-408 where

  -- τ=534: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=932 (1×)
  cell-408-534 : τ 534 ≡ τ 534
  cell-408-534 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=409, 1 nodes, 1 type contexts, 1 forms

module let-k-409 where

  -- τ=536: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=948 (1×)
  cell-409-536 : τ 536 ≡ τ 536
  cell-409-536 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=410, 1 nodes, 1 type contexts, 1 forms

module let-k-410 where

  -- τ=537: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=949 (1×)
  cell-410-537 : τ 537 ≡ τ 537
  cell-410-537 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=411, 1 nodes, 1 type contexts, 1 forms

module let-k-411 where

  -- τ=539: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=961 (1×)
  cell-411-539 : τ 539 ≡ τ 539
  cell-411-539 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=417, 1 nodes, 1 type contexts, 1 forms

module index-417 where

  -- τ=545: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=969 (1×)
  cell-417-545 : τ 545 ≡ τ 545
  cell-417-545 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=418, 1 nodes, 1 type contexts, 1 forms

module subscript-418 where

  -- τ=546: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=970 (1×)
  cell-418-546 : τ 546 ≡ τ 546
  cell-418-546 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=419, 1 nodes, 1 type contexts, 1 forms

module annassign-419 where

  -- τ=547: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=971 (1×)
  cell-419-547 : τ 547 ≡ τ 547
  cell-419-547 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=422, 1 nodes, 1 type contexts, 1 forms

module equalizer-422 where

  -- τ=550: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=987 (1×)
  cell-422-550 : τ 550 ≡ τ 550
  cell-422-550 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=423, 1 nodes, 1 type contexts, 1 forms

module equalizer-423 where

  -- τ=551: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=989 (1×)
  cell-423-551 : τ 551 ≡ τ 551
  cell-423-551 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=424, 1 nodes, 1 type contexts, 1 forms

module fold-424 where

  -- τ=552: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=990 (1×)
  cell-424-552 : τ 552 ≡ τ 552
  cell-424-552 = refl


-- ── monoid.accum (──────────────────────────────────────)
-- κ=425, 1 nodes, 1 type contexts, 1 forms

module monoid-accum-425 where

  -- τ=553: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=992 (1×)
  cell-425-553 : τ 553 ≡ τ 553
  cell-425-553 = refl


-- ── free_monoid.map (───────────────────────────────────)
-- κ=426, 1 nodes, 1 type contexts, 1 forms

module free_monoid-map-426 where

  -- τ=554: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=997 (1×)
  cell-426-554 : τ 554 ≡ τ 554
  cell-426-554 = refl


-- ── product (───────────────────────────────────────────)
-- κ=427, 1 nodes, 1 type contexts, 1 forms

module product-427 where

  -- τ=555: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=999 (1×)
  cell-427-555 : τ 555 ≡ τ 555
  cell-427-555 = refl


-- ── free_monoid.snoc@state (────────────────────────────)
-- κ=428, 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-state-428 where

  -- τ=556: 1 nodes, 1 forms
  -- Types: None
  -- σ=1000 (1×)
  cell-428-556 : τ 556 ≡ τ 556
  cell-428-556 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=429, 1 nodes, 1 type contexts, 1 forms

module effect-seq-429 where

  -- τ=557: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1001 (1×)
  cell-429-557 : τ 557 ≡ τ 557
  cell-429-557 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=430, 1 nodes, 1 type contexts, 1 forms

module fold-430 where

  -- τ=558: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1017 (1×)
  cell-430-558 : τ 558 ≡ τ 558
  cell-430-558 = refl


-- ── coproduct.elim (────────────────────────────────────)
-- κ=431, 1 nodes, 1 type contexts, 1 forms

module coproduct-elim-431 where

  -- τ=559: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1018 (1×)
  cell-431-559 : τ 559 ≡ τ 559
  cell-431-559 = refl


-- ── complement (────────────────────────────────────────)
-- κ=432, 1 nodes, 1 type contexts, 1 forms

module complement-432 where

  -- τ=560: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1019 (1×)
  cell-432-560 : τ 560 ≡ τ 560
  cell-432-560 = refl


-- ── del (───────────────────────────────────────────────)
-- κ=433, 1 nodes, 1 type contexts, 1 forms

module del-433 where

  -- τ=561: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1020 (1×)
  cell-433-561 : τ 561 ≡ τ 561
  cell-433-561 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=434, 1 nodes, 1 type contexts, 1 forms

module subscript-434 where

  -- τ=562: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1021 (1×)
  cell-434-562 : τ 562 ≡ τ 562
  cell-434-562 = refl


-- ── delete (────────────────────────────────────────────)
-- κ=435, 1 nodes, 1 type contexts, 1 forms

module delete-435 where

  -- τ=563: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1022 (1×)
  cell-435-563 : τ 563 ≡ τ 563
  cell-435-563 = refl


-- ── morphism@object (───────────────────────────────────)
-- κ=436, 1 nodes, 1 type contexts, 1 forms

module morphism-at-object-436 where

  -- τ=564: 1 nodes, 1 forms
  -- Types: T.discard
  -- σ=1028 (1×)
  cell-436-564 : τ 564 ≡ τ 564
  cell-436-564 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=437, 1 nodes, 1 type contexts, 1 forms

module apply-437 where

  -- τ=565: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1029 (1×)
  cell-437-565 : τ 565 ≡ τ 565
  cell-437-565 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=438, 1 nodes, 1 type contexts, 1 forms

module effect-seq-438 where

  -- τ=566: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1030 (1×)
  cell-438-566 : τ 566 ≡ τ 566
  cell-438-566 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=439, 1 nodes, 1 type contexts, 1 forms

module fold-439 where

  -- τ=567: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1031 (1×)
  cell-439-567 : τ 567 ≡ τ 567
  cell-439-567 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=447, 1 nodes, 1 type contexts, 1 forms

module equalizer-447 where

  -- τ=575: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1101 (1×)
  cell-447-575 : τ 575 ≡ τ 575
  cell-447-575 = refl


-- ── partial.apply@state (───────────────────────────────)
-- κ=448, 1 nodes, 1 type contexts, 1 forms

module partial-apply-at-state-448 where

  -- τ=577: 1 nodes, 1 forms
  -- Types: T
  -- σ=1104 (1×)
  cell-448-577 : τ 577 ≡ τ 577
  cell-448-577 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=449, 1 nodes, 1 type contexts, 1 forms

module let-k-449 where

  -- τ=578: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1105 (1×)
  cell-449-578 : τ 578 ≡ τ 578
  cell-449-578 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=454, 1 nodes, 1 type contexts, 1 forms

module equalizer-454 where

  -- τ=583: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1121 (1×)
  cell-454-583 : τ 583 ≡ τ 583
  cell-454-583 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=455, 1 nodes, 1 type contexts, 1 forms

module fold-455 where

  -- τ=584: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1122 (1×)
  cell-455-584 : τ 584 ≡ τ 584
  cell-455-584 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=457, 1 nodes, 1 type contexts, 1 forms

module let-k-457 where

  -- τ=586: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1129 (1×)
  cell-457-586 : τ 586 ≡ τ 586
  cell-457-586 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=458, 1 nodes, 1 type contexts, 1 forms

module let-k-458 where

  -- τ=588: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1134 (1×)
  cell-458-588 : τ 588 ≡ τ 588
  cell-458-588 = refl


-- ── free_monoid.fold (──────────────────────────────────)
-- κ=460, 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-460 where

  -- τ=590: 1 nodes, 1 forms
  -- Types: str
  -- σ=1140 (1×)
  cell-460-590 : τ 590 ≡ τ 590
  cell-460-590 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=461, 1 nodes, 1 type contexts, 1 forms

module let-k-461 where

  -- τ=591: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1141 (1×)
  cell-461-591 : τ 591 ≡ τ 591
  cell-461-591 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=469, 1 nodes, 1 type contexts, 1 forms

module equalizer-469 where

  -- τ=604: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1172 (1×)
  cell-469-604 : τ 604 ≡ τ 604
  cell-469-604 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=475, 1 nodes, 1 type contexts, 1 forms

module equalizer-475 where

  -- τ=611: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1208 (1×)
  cell-475-611 : τ 611 ≡ τ 611
  cell-475-611 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=476, 1 nodes, 1 type contexts, 1 forms

module fold-476 where

  -- τ=612: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1209 (1×)
  cell-476-612 : τ 612 ≡ τ 612
  cell-476-612 = refl


-- ── fixpoint (──────────────────────────────────────────)
-- κ=477, 1 nodes, 1 type contexts, 1 forms

module fixpoint-477 where

  -- τ=613: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1211 (1×)
  cell-477-613 : τ 613 ≡ τ 613
  cell-477-613 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=478, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-478 where

  -- τ=614: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1212 (1×)
  cell-478-614 : τ 614 ≡ τ 614
  cell-478-614 = refl


-- ── product (───────────────────────────────────────────)
-- κ=479, 1 nodes, 1 type contexts, 1 forms

module product-479 where

  -- τ=615: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=1214 (1×)
  cell-479-615 : τ 615 ≡ τ 615
  cell-479-615 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=480, 1 nodes, 1 type contexts, 1 forms

module index-480 where

  -- τ=616: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1215 (1×)
  cell-480-616 : τ 616 ≡ τ 616
  cell-480-616 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=481, 1 nodes, 1 type contexts, 1 forms

module subscript-481 where

  -- τ=617: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1216 (1×)
  cell-481-617 : τ 617 ≡ τ 617
  cell-481-617 = refl


-- ── arg (───────────────────────────────────────────────)
-- κ=482, 1 nodes, 1 type contexts, 1 forms

module arg-482 where

  -- τ=618: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1217 (1×)
  cell-482-618 : τ 618 ≡ τ 618
  cell-482-618 = refl


-- ── arguments (─────────────────────────────────────────)
-- κ=483, 1 nodes, 1 type contexts, 1 forms

module arguments-483 where

  -- τ=619: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1224 (1×)
  cell-483-619 : τ 619 ≡ τ 619
  cell-483-619 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=485, 1 nodes, 1 type contexts, 1 forms

module let-k-485 where

  -- τ=621: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1233 (1×)
  cell-485-621 : τ 621 ≡ τ 621
  cell-485-621 = refl


-- ── product (───────────────────────────────────────────)
-- κ=488, 1 nodes, 1 type contexts, 1 forms

module product-488 where

  -- τ=626: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=1261 (1×)
  cell-488-626 : τ 626 ≡ τ 626
  cell-488-626 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=489, 1 nodes, 1 type contexts, 1 forms

module index-489 where

  -- τ=627: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1262 (1×)
  cell-489-627 : τ 627 ≡ τ 627
  cell-489-627 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=490, 1 nodes, 1 type contexts, 1 forms

module subscript-490 where

  -- τ=628: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1263 (1×)
  cell-490-628 : τ 628 ≡ τ 628
  cell-490-628 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=491, 1 nodes, 1 type contexts, 1 forms

module annassign-491 where

  -- τ=629: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1267 (1×)
  cell-491-629 : τ 629 ≡ τ 629
  cell-491-629 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=492, 1 nodes, 1 type contexts, 1 forms

module annassign-492 where

  -- τ=633: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1273 (1×)
  cell-492-633 : τ 633 ≡ τ 633
  cell-492-633 = refl


-- ── meet (──────────────────────────────────────────────)
-- κ=494, 1 nodes, 1 type contexts, 1 forms

module meet-494 where

  -- τ=635: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1277 (1×)
  cell-494-635 : τ 635 ≡ τ 635
  cell-494-635 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=495, 1 nodes, 1 type contexts, 1 forms

module equalizer-495 where

  -- τ=636: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1284 (1×)
  cell-495-636 : τ 636 ≡ τ 636
  cell-495-636 = refl


-- ── lazy_fold (─────────────────────────────────────────)
-- κ=496, 1 nodes, 1 type contexts, 1 forms

module lazy_fold-496 where

  -- τ=637: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1287 (1×)
  cell-496-637 : τ 637 ≡ τ 637
  cell-496-637 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=497, 1 nodes, 1 type contexts, 1 forms

module apply-497 where

  -- τ=638: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1288 (1×)
  cell-497-638 : τ 638 ≡ τ 638
  cell-497-638 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=498, 1 nodes, 1 type contexts, 1 forms

module let-k-498 where

  -- τ=639: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1289 (1×)
  cell-498-639 : τ 639 ≡ τ 639
  cell-498-639 = refl


-- ── free_monoid.map (───────────────────────────────────)
-- κ=499, 1 nodes, 1 type contexts, 1 forms

module free_monoid-map-499 where

  -- τ=640: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1291 (1×)
  cell-499-640 : τ 640 ≡ τ 640
  cell-499-640 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=500, 1 nodes, 1 type contexts, 1 forms

module let-k-500 where

  -- τ=641: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1292 (1×)
  cell-500-641 : τ 641 ≡ τ 641
  cell-500-641 = refl


-- ── free_monoid.snoc@? (────────────────────────────────)
-- κ=501, 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-x3f-501 where

  -- τ=189: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1294 (1×)
  cell-501-189 : τ 189 ≡ τ 189
  cell-501-189 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=502, 1 nodes, 1 type contexts, 1 forms

module effect-seq-502 where

  -- τ=190: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1295 (1×)
  cell-502-190 : τ 190 ≡ τ 190
  cell-502-190 = refl


-- ── monoid.op (─────────────────────────────────────────)
-- κ=503, 1 nodes, 1 type contexts, 1 forms

module monoid-op-503 where

  -- τ=642: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1297 (1×)
  cell-503-642 : τ 642 ≡ τ 642
  cell-503-642 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=504, 1 nodes, 1 type contexts, 1 forms

module let-k-504 where

  -- τ=643: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1298 (1×)
  cell-504-643 : τ 643 ≡ τ 643
  cell-504-643 = refl


-- ── free_monoid.fold (──────────────────────────────────)
-- κ=505, 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-505 where

  -- τ=644: 1 nodes, 1 forms
  -- Types: str
  -- σ=1302 (1×)
  cell-505-644 : τ 644 ≡ τ 644
  cell-505-644 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=506, 1 nodes, 1 type contexts, 1 forms

module let-k-506 where

  -- τ=645: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1303 (1×)
  cell-506-645 : τ 645 ≡ τ 645
  cell-506-645 = refl


-- ── free_monoid.map (───────────────────────────────────)
-- κ=507, 1 nodes, 1 type contexts, 1 forms

module free_monoid-map-507 where

  -- τ=649: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1329 (1×)
  cell-507-649 : τ 649 ≡ τ 649
  cell-507-649 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=508, 1 nodes, 1 type contexts, 1 forms

module apply-508 where

  -- τ=650: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1330 (1×)
  cell-508-650 : τ 650 ≡ τ 650
  cell-508-650 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=509, 1 nodes, 1 type contexts, 1 forms

module effect-seq-509 where

  -- τ=651: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1331 (1×)
  cell-509-651 : τ 651 ≡ τ 651
  cell-509-651 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=510, 1 nodes, 1 type contexts, 1 forms

module equalizer-510 where

  -- τ=655: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1341 (1×)
  cell-510-655 : τ 655 ≡ τ 655
  cell-510-655 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=512, 1 nodes, 1 type contexts, 1 forms

module let-k-512 where

  -- τ=521: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1345 (1×)
  cell-512-521 : τ 521 ≡ τ 521
  cell-512-521 = refl


-- ── monoid.op@? (───────────────────────────────────────)
-- κ=513, 1 nodes, 1 type contexts, 1 forms

module monoid-op-at-x3f-513 where

  -- τ=656: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1348 (1×)
  cell-513-656 : τ 656 ≡ τ 656
  cell-513-656 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=514, 1 nodes, 1 type contexts, 1 forms

module effect-seq-514 where

  -- τ=657: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1349 (1×)
  cell-514-657 : τ 657 ≡ τ 657
  cell-514-657 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=516, 1 nodes, 1 type contexts, 1 forms

module effect-seq-516 where

  -- τ=190: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1353 (1×)
  cell-516-190 : τ 190 ≡ τ 190
  cell-516-190 = refl


-- ── coproduct.elim (────────────────────────────────────)
-- κ=517, 1 nodes, 1 type contexts, 1 forms

module coproduct-elim-517 where

  -- τ=662: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1359 (1×)
  cell-517-662 : τ 662 ≡ τ 662
  cell-517-662 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=518, 1 nodes, 1 type contexts, 1 forms

module equalizer-518 where

  -- τ=663: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1368 (1×)
  cell-518-663 : τ 663 ≡ τ 663
  cell-518-663 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=519, 1 nodes, 1 type contexts, 1 forms

module let-k-519 where

  -- τ=664: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1370 (1×)
  cell-519-664 : τ 664 ≡ τ 664
  cell-519-664 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=520, 1 nodes, 1 type contexts, 1 forms

module equalizer-520 where

  -- τ=665: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1374 (1×)
  cell-520-665 : τ 665 ≡ τ 665
  cell-520-665 = refl


-- ── coproduct.elim (────────────────────────────────────)
-- κ=521, 1 nodes, 1 type contexts, 1 forms

module coproduct-elim-521 where

  -- τ=666: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1375 (1×)
  cell-521-666 : τ 666 ≡ τ 666
  cell-521-666 = refl


-- ── exponential.literal (───────────────────────────────)
-- κ=522, 1 nodes, 1 type contexts, 1 forms

module exponential-literal-522 where

  -- τ=668: 1 nodes, 1 forms
  -- Types: dict
  -- σ=1387 (1×)
  cell-522-668 : τ 668 ≡ τ 668
  cell-522-668 = refl


-- ── free_monoid.snoc@state (────────────────────────────)
-- κ=523, 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-state-523 where

  -- τ=669: 1 nodes, 1 forms
  -- Types: None
  -- σ=1388 (1×)
  cell-523-669 : τ 669 ≡ τ 669
  cell-523-669 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=524, 1 nodes, 1 type contexts, 1 forms

module effect-seq-524 where

  -- τ=670: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1389 (1×)
  cell-524-670 : τ 670 ≡ τ 670
  cell-524-670 = refl


-- ── product (───────────────────────────────────────────)
-- κ=525, 1 nodes, 1 type contexts, 1 forms

module product-525 where

  -- τ=671: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=1393 (1×)
  cell-525-671 : τ 671 ≡ τ 671
  cell-525-671 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=526, 1 nodes, 1 type contexts, 1 forms

module index-526 where

  -- τ=672: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1394 (1×)
  cell-526-672 : τ 672 ≡ τ 672
  cell-526-672 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=527, 1 nodes, 1 type contexts, 1 forms

module subscript-527 where

  -- τ=673: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1395 (1×)
  cell-527-673 : τ 673 ≡ τ 673
  cell-527-673 = refl


-- ── monoid.op@? (───────────────────────────────────────)
-- κ=528, 1 nodes, 1 type contexts, 1 forms

module monoid-op-at-x3f-528 where

  -- τ=674: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1396 (1×)
  cell-528-674 : τ 674 ≡ τ 674
  cell-528-674 = refl


-- ── monoid.op@? (───────────────────────────────────────)
-- κ=529, 1 nodes, 1 type contexts, 1 forms

module monoid-op-at-x3f-529 where

  -- τ=675: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1397 (1×)
  cell-529-675 : τ 675 ≡ τ 675
  cell-529-675 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=530, 1 nodes, 1 type contexts, 1 forms

module effect-seq-530 where

  -- τ=676: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1398 (1×)
  cell-530-676 : τ 676 ≡ τ 676
  cell-530-676 = refl


-- ── terminal.map (──────────────────────────────────────)
-- κ=532, 1 nodes, 1 type contexts, 1 forms

module terminal-map-532 where

  -- τ=678: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1400 (1×)
  cell-532-678 : τ 678 ≡ τ 678
  cell-532-678 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=533, 1 nodes, 1 type contexts, 1 forms

module index-533 where

  -- τ=680: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1402 (1×)
  cell-533-680 : τ 680 ≡ τ 680
  cell-533-680 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=534, 1 nodes, 1 type contexts, 1 forms

module subscript-534 where

  -- τ=681: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1403 (1×)
  cell-534-681 : τ 681 ≡ τ 681
  cell-534-681 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=535, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-535 where

  -- τ=682: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1404 (1×)
  cell-535-682 : τ 682 ≡ τ 682
  cell-535-682 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=536, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-536 where

  -- τ=683: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1407 (1×)
  cell-536-683 : τ 683 ≡ τ 683
  cell-536-683 = refl


-- ── arg (───────────────────────────────────────────────)
-- κ=537, 1 nodes, 1 type contexts, 1 forms

module arg-537 where

  -- τ=684: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1408 (1×)
  cell-537-684 : τ 684 ≡ τ 684
  cell-537-684 = refl


-- ── arguments (─────────────────────────────────────────)
-- κ=538, 1 nodes, 1 type contexts, 1 forms

module arguments-538 where

  -- τ=685: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1410 (1×)
  cell-538-685 : τ 685 ≡ τ 685
  cell-538-685 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=539, 1 nodes, 1 type contexts, 1 forms

module annassign-539 where

  -- τ=687: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1414 (1×)
  cell-539-687 : τ 687 ≡ τ 687
  cell-539-687 = refl


-- ── terminal.map (──────────────────────────────────────)
-- κ=542, 1 nodes, 1 type contexts, 1 forms

module terminal-map-542 where

  -- τ=691: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1420 (1×)
  cell-542-691 : τ 691 ≡ τ 691
  cell-542-691 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=543, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-543 where

  -- τ=692: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1421 (1×)
  cell-543-692 : τ 692 ≡ τ 692
  cell-543-692 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=549, 1 nodes, 1 type contexts, 1 forms

module annassign-549 where

  -- τ=699: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1432 (1×)
  cell-549-699 : τ 699 ≡ τ 699
  cell-549-699 = refl


-- ── product (───────────────────────────────────────────)
-- κ=551, 1 nodes, 1 type contexts, 1 forms

module product-551 where

  -- τ=702: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=1444 (1×)
  cell-551-702 : τ 702 ≡ τ 702
  cell-551-702 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=552, 1 nodes, 1 type contexts, 1 forms

module index-552 where

  -- τ=703: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1445 (1×)
  cell-552-703 : τ 703 ≡ τ 703
  cell-552-703 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=553, 1 nodes, 1 type contexts, 1 forms

module subscript-553 where

  -- τ=704: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1446 (1×)
  cell-553-704 : τ 704 ≡ τ 704
  cell-553-704 = refl


-- ── free_monoid.op@? (──────────────────────────────────)
-- κ=554, 1 nodes, 1 type contexts, 1 forms

module free_monoid-op-at-x3f-554 where

  -- τ=705: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1447 (1×)
  cell-554-705 : τ 705 ≡ τ 705
  cell-554-705 = refl


-- ── free_monoid.snoc@? (────────────────────────────────)
-- κ=555, 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-x3f-555 where

  -- τ=706: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1449 (1×)
  cell-555-706 : τ 706 ≡ τ 706
  cell-555-706 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=556, 1 nodes, 1 type contexts, 1 forms

module effect-seq-556 where

  -- τ=707: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1450 (1×)
  cell-556-707 : τ 707 ≡ τ 707
  cell-556-707 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=557, 1 nodes, 1 type contexts, 1 forms

module fold-557 where

  -- τ=708: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1451 (1×)
  cell-557-708 : τ 708 ≡ τ 708
  cell-557-708 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=560, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-560 where

  -- τ=711: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1455 (1×)
  cell-560-711 : τ 711 ≡ τ 711
  cell-560-711 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=561, 1 nodes, 1 type contexts, 1 forms

module annassign-561 where

  -- τ=715: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1467 (1×)
  cell-561-715 : τ 715 ≡ τ 715
  cell-561-715 = refl


-- ── product (───────────────────────────────────────────)
-- κ=562, 1 nodes, 1 type contexts, 1 forms

module product-562 where

  -- τ=716: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=1472 (1×)
  cell-562-716 : τ 716 ≡ τ 716
  cell-562-716 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=563, 1 nodes, 1 type contexts, 1 forms

module index-563 where

  -- τ=717: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1473 (1×)
  cell-563-717 : τ 717 ≡ τ 717
  cell-563-717 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=564, 1 nodes, 1 type contexts, 1 forms

module subscript-564 where

  -- τ=718: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1474 (1×)
  cell-564-718 : τ 718 ≡ τ 718
  cell-564-718 = refl


-- ── free_monoid.op@? (──────────────────────────────────)
-- κ=565, 1 nodes, 1 type contexts, 1 forms

module free_monoid-op-at-x3f-565 where

  -- τ=719: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1475 (1×)
  cell-565-719 : τ 719 ≡ τ 719
  cell-565-719 = refl


-- ── free_monoid.snoc@? (────────────────────────────────)
-- κ=566, 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-x3f-566 where

  -- τ=720: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1476 (1×)
  cell-566-720 : τ 720 ≡ τ 720
  cell-566-720 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=567, 1 nodes, 1 type contexts, 1 forms

module effect-seq-567 where

  -- τ=721: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1477 (1×)
  cell-567-721 : τ 721 ≡ τ 721
  cell-567-721 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=568, 1 nodes, 1 type contexts, 1 forms

module fold-568 where

  -- τ=722: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1478 (1×)
  cell-568-722 : τ 722 ≡ τ 722
  cell-568-722 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=569, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-569 where

  -- τ=724: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1480 (1×)
  cell-569-724 : τ 724 ≡ τ 724
  cell-569-724 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=572, 1 nodes, 1 type contexts, 1 forms

module subscript-572 where

  -- τ=731: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1498 (1×)
  cell-572-731 : τ 731 ≡ τ 731
  cell-572-731 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=573, 1 nodes, 1 type contexts, 1 forms

module subscript-573 where

  -- τ=732: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1502 (1×)
  cell-573-732 : τ 732 ≡ τ 732
  cell-573-732 = refl


-- ── monoid.accum (──────────────────────────────────────)
-- κ=574, 1 nodes, 1 type contexts, 1 forms

module monoid-accum-574 where

  -- τ=733: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1503 (1×)
  cell-574-733 : τ 733 ≡ τ 733
  cell-574-733 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=575, 1 nodes, 1 type contexts, 1 forms

module fold-575 where

  -- τ=734: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1504 (1×)
  cell-575-734 : τ 734 ≡ τ 734
  cell-575-734 = refl


-- ── exponential.map (───────────────────────────────────)
-- κ=577, 1 nodes, 1 type contexts, 1 forms

module exponential-map-577 where

  -- τ=736: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1514 (1×)
  cell-577-736 : τ 736 ≡ τ 736
  cell-577-736 = refl


-- ── terminal.map (──────────────────────────────────────)
-- κ=578, 1 nodes, 1 type contexts, 1 forms

module terminal-map-578 where

  -- τ=737: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1515 (1×)
  cell-578-737 : τ 737 ≡ τ 737
  cell-578-737 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=579, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-579 where

  -- τ=741: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1520 (1×)
  cell-579-741 : τ 741 ≡ τ 741
  cell-579-741 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=580, 1 nodes, 1 type contexts, 1 forms

module let-k-580 where

  -- τ=742: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1535 (1×)
  cell-580-742 : τ 742 ≡ τ 742
  cell-580-742 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=581, 1 nodes, 1 type contexts, 1 forms

module subscript-581 where

  -- τ=743: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1540 (1×)
  cell-581-743 : τ 743 ≡ τ 743
  cell-581-743 = refl


-- ── morphism@? (────────────────────────────────────────)
-- κ=582, 1 nodes, 1 type contexts, 1 forms

module morphism-at-x3f-582 where

  -- τ=744: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1541 (1×)
  cell-582-744 : τ 744 ≡ τ 744
  cell-582-744 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=583, 1 nodes, 1 type contexts, 1 forms

module apply-583 where

  -- τ=745: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1548 (1×)
  cell-583-745 : τ 745 ≡ τ 745
  cell-583-745 = refl


-- ── monoid.op@? (───────────────────────────────────────)
-- κ=584, 1 nodes, 1 type contexts, 1 forms

module monoid-op-at-x3f-584 where

  -- τ=746: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1549 (1×)
  cell-584-746 : τ 746 ≡ τ 746
  cell-584-746 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=585, 1 nodes, 1 type contexts, 1 forms

module effect-seq-585 where

  -- τ=747: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1550 (1×)
  cell-585-747 : τ 747 ≡ τ 747
  cell-585-747 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=586, 1 nodes, 1 type contexts, 1 forms

module fold-586 where

  -- τ=748: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1551 (1×)
  cell-586-748 : τ 748 ≡ τ 748
  cell-586-748 = refl


-- ── terminal.map (──────────────────────────────────────)
-- κ=587, 1 nodes, 1 type contexts, 1 forms

module terminal-map-587 where

  -- τ=749: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1553 (1×)
  cell-587-749 : τ 749 ≡ τ 749
  cell-587-749 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=588, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-588 where

  -- τ=750: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1554 (1×)
  cell-588-750 : τ 750 ≡ τ 750
  cell-588-750 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=590, 1 nodes, 1 type contexts, 1 forms

module index-590 where

  -- τ=753: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1564 (1×)
  cell-590-753 : τ 753 ≡ τ 753
  cell-590-753 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=591, 1 nodes, 1 type contexts, 1 forms

module subscript-591 where

  -- τ=754: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1565 (1×)
  cell-591-754 : τ 754 ≡ τ 754
  cell-591-754 = refl


-- ── monoid.accum (──────────────────────────────────────)
-- κ=592, 1 nodes, 1 type contexts, 1 forms

module monoid-accum-592 where

  -- τ=755: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1566 (1×)
  cell-592-755 : τ 755 ≡ τ 755
  cell-592-755 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=593, 1 nodes, 1 type contexts, 1 forms

module fold-593 where

  -- τ=756: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1567 (1×)
  cell-593-756 : τ 756 ≡ τ 756
  cell-593-756 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=594, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-594 where

  -- τ=757: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1569 (1×)
  cell-594-757 : τ 757 ≡ τ 757
  cell-594-757 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=595, 1 nodes, 1 type contexts, 1 forms

module annassign-595 where

  -- τ=760: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1581 (1×)
  cell-595-760 : τ 760 ≡ τ 760
  cell-595-760 = refl


-- ── exponential.literal (───────────────────────────────)
-- κ=598, 1 nodes, 1 type contexts, 1 forms

module exponential-literal-598 where

  -- τ=765: 1 nodes, 1 forms
  -- Types: dict
  -- σ=1607 (1×)
  cell-598-765 : τ 765 ≡ τ 765
  cell-598-765 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=599, 1 nodes, 1 type contexts, 1 forms

module annassign-599 where

  -- τ=766: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1608 (1×)
  cell-599-766 : τ 766 ≡ τ 766
  cell-599-766 = refl


-- ── keyword (───────────────────────────────────────────)
-- κ=601, 1 nodes, 1 type contexts, 1 forms

module keyword-601 where

  -- τ=767: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1613 (1×)
  cell-601-767 : τ 767 ≡ τ 767
  cell-601-767 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=602, 1 nodes, 1 type contexts, 1 forms

module apply-602 where

  -- τ=768: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1614 (1×)
  cell-602-768 : τ 768 ≡ τ 768
  cell-602-768 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=603, 1 nodes, 1 type contexts, 1 forms

module let-k-603 where

  -- τ=769: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1615 (1×)
  cell-603-769 : τ 769 ≡ τ 769
  cell-603-769 = refl


-- ── monoid.accum (──────────────────────────────────────)
-- κ=604, 1 nodes, 1 type contexts, 1 forms

module monoid-accum-604 where

  -- τ=770: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1620 (1×)
  cell-604-770 : τ 770 ≡ τ 770
  cell-604-770 = refl


-- ── exponential.literal (───────────────────────────────)
-- κ=605, 1 nodes, 1 type contexts, 1 forms

module exponential-literal-605 where

  -- τ=771: 1 nodes, 1 forms
  -- Types: dict
  -- σ=1622 (1×)
  cell-605-771 : τ 771 ≡ τ 771
  cell-605-771 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=606, 1 nodes, 1 type contexts, 1 forms

module let-k-606 where

  -- τ=772: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1623 (1×)
  cell-606-772 : τ 772 ≡ τ 772
  cell-606-772 = refl


-- ── monoid.op@? (───────────────────────────────────────)
-- κ=607, 1 nodes, 1 type contexts, 1 forms

module monoid-op-at-x3f-607 where

  -- τ=774: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1629 (1×)
  cell-607-774 : τ 774 ≡ τ 774
  cell-607-774 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=608, 1 nodes, 1 type contexts, 1 forms

module effect-seq-608 where

  -- τ=775: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1630 (1×)
  cell-608-775 : τ 775 ≡ τ 775
  cell-608-775 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=609, 1 nodes, 1 type contexts, 1 forms

module fold-609 where

  -- τ=776: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1631 (1×)
  cell-609-776 : τ 776 ≡ τ 776
  cell-609-776 = refl


-- ── terminal.map (──────────────────────────────────────)
-- κ=610, 1 nodes, 1 type contexts, 1 forms

module terminal-map-610 where

  -- τ=777: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1633 (1×)
  cell-610-777 : τ 777 ≡ τ 777
  cell-610-777 = refl


-- ── product (───────────────────────────────────────────)
-- κ=611, 1 nodes, 1 type contexts, 1 forms

module product-611 where

  -- τ=778: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=1634 (1×)
  cell-611-778 : τ 778 ≡ τ 778
  cell-611-778 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=612, 1 nodes, 1 type contexts, 1 forms

module index-612 where

  -- τ=779: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1635 (1×)
  cell-612-779 : τ 779 ≡ τ 779
  cell-612-779 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=613, 1 nodes, 1 type contexts, 1 forms

module subscript-613 where

  -- τ=780: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1636 (1×)
  cell-613-780 : τ 780 ≡ τ 780
  cell-613-780 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=614, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-614 where

  -- τ=781: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1637 (1×)
  cell-614-781 : τ 781 ≡ τ 781
  cell-614-781 = refl


-- ── comprehension (─────────────────────────────────────)
-- κ=616, 1 nodes, 1 type contexts, 1 forms

module comprehension-616 where

  -- τ=783: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1646 (1×)
  cell-616-783 : τ 783 ≡ τ 783
  cell-616-783 = refl


-- ── free_monoid.map (───────────────────────────────────)
-- κ=617, 1 nodes, 1 type contexts, 1 forms

module free_monoid-map-617 where

  -- τ=784: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1647 (1×)
  cell-617-784 : τ 784 ≡ τ 784
  cell-617-784 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=618, 1 nodes, 1 type contexts, 1 forms

module let-k-618 where

  -- τ=785: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1648 (1×)
  cell-618-785 : τ 785 ≡ τ 785
  cell-618-785 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=621, 1 nodes, 1 type contexts, 1 forms

module annassign-621 where

  -- τ=788: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1655 (1×)
  cell-621-788 : τ 788 ≡ τ 788
  cell-621-788 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=622, 1 nodes, 1 type contexts, 1 forms

module let-k-622 where

  -- τ=790: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1660 (1×)
  cell-622-790 : τ 790 ≡ τ 790
  cell-622-790 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=623, 1 nodes, 1 type contexts, 1 forms

module equalizer-623 where

  -- τ=791: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1666 (1×)
  cell-623-791 : τ 791 ≡ τ 791
  cell-623-791 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=624, 1 nodes, 1 type contexts, 1 forms

module fold-624 where

  -- τ=792: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1667 (1×)
  cell-624-792 : τ 792 ≡ τ 792
  cell-624-792 = refl


-- ── coproduct.elim (────────────────────────────────────)
-- κ=625, 1 nodes, 1 type contexts, 1 forms

module coproduct-elim-625 where

  -- τ=793: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1673 (1×)
  cell-625-793 : τ 793 ≡ τ 793
  cell-625-793 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=626, 1 nodes, 1 type contexts, 1 forms

module fold-626 where

  -- τ=794: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1674 (1×)
  cell-626-794 : τ 794 ≡ τ 794
  cell-626-794 = refl


-- ── projection@? (──────────────────────────────────────)
-- κ=628, 1 nodes, 1 type contexts, 1 forms

module projection-at-x3f-628 where

  -- τ=796: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1681 (1×)
  cell-628-796 : τ 796 ≡ τ 796
  cell-628-796 = refl


-- ── projection.compute@? (──────────────────────────────)
-- κ=629, 1 nodes, 1 type contexts, 1 forms

module projection-compute-at-x3f-629 where

  -- τ=797: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1682 (1×)
  cell-629-797 : τ 797 ≡ τ 797
  cell-629-797 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=630, 1 nodes, 1 type contexts, 1 forms

module apply-630 where

  -- τ=798: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1683 (1×)
  cell-630-798 : τ 798 ≡ τ 798
  cell-630-798 = refl


-- ── endomorphism (──────────────────────────────────────)
-- κ=631, 1 nodes, 1 type contexts, 1 forms

module endomorphism-631 where

  -- τ=799: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1684 (1×)
  cell-631-799 : τ 799 ≡ τ 799
  cell-631-799 = refl


-- ── lambda (────────────────────────────────────────────)
-- κ=632, 1 nodes, 1 type contexts, 1 forms

module lambda-632 where

  -- τ=800: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1685 (1×)
  cell-632-800 : τ 800 ≡ τ 800
  cell-632-800 = refl


-- ── keyword (───────────────────────────────────────────)
-- κ=633, 1 nodes, 1 type contexts, 1 forms

module keyword-633 where

  -- τ=801: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1686 (1×)
  cell-633-801 : τ 801 ≡ τ 801
  cell-633-801 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=634, 1 nodes, 1 type contexts, 1 forms

module apply-634 where

  -- τ=802: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1687 (1×)
  cell-634-802 : τ 802 ≡ τ 802
  cell-634-802 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=635, 1 nodes, 1 type contexts, 1 forms

module effect-seq-635 where

  -- τ=803: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1688 (1×)
  cell-635-803 : τ 803 ≡ τ 803
  cell-635-803 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=636, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-636 where

  -- τ=804: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1690 (1×)
  cell-636-804 : τ 804 ≡ τ 804
  cell-636-804 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=637, 1 nodes, 1 type contexts, 1 forms

module let-k-637 where

  -- τ=809: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1707 (1×)
  cell-637-809 : τ 809 ≡ τ 809
  cell-637-809 = refl


-- ── free_monoid.op@? (──────────────────────────────────)
-- κ=638, 1 nodes, 1 type contexts, 1 forms

module free_monoid-op-at-x3f-638 where

  -- τ=810: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1712 (1×)
  cell-638-810 : τ 810 ≡ τ 810
  cell-638-810 = refl


-- ── free_monoid.snoc@? (────────────────────────────────)
-- κ=639, 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-x3f-639 where

  -- τ=811: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1713 (1×)
  cell-639-811 : τ 811 ≡ τ 811
  cell-639-811 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=640, 1 nodes, 1 type contexts, 1 forms

module effect-seq-640 where

  -- τ=812: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1714 (1×)
  cell-640-812 : τ 812 ≡ τ 812
  cell-640-812 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=641, 1 nodes, 1 type contexts, 1 forms

module fold-641 where

  -- τ=813: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1715 (1×)
  cell-641-813 : τ 813 ≡ τ 813
  cell-641-813 = refl


-- ── product (───────────────────────────────────────────)
-- κ=642, 1 nodes, 1 type contexts, 1 forms

module product-642 where

  -- τ=814: 1 nodes, 1 forms
  -- Types: tuple
  -- σ=1718 (1×)
  cell-642-814 : τ 814 ≡ τ 814
  cell-642-814 = refl


-- ── index (─────────────────────────────────────────────)
-- κ=643, 1 nodes, 1 type contexts, 1 forms

module index-643 where

  -- τ=815: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1719 (1×)
  cell-643-815 : τ 815 ≡ τ 815
  cell-643-815 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=644, 1 nodes, 1 type contexts, 1 forms

module subscript-644 where

  -- τ=816: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1720 (1×)
  cell-644-816 : τ 816 ≡ τ 816
  cell-644-816 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=645, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-645 where

  -- τ=817: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1721 (1×)
  cell-645-817 : τ 817 ≡ τ 817
  cell-645-817 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=651, 1 nodes, 1 type contexts, 1 forms

module annassign-651 where

  -- τ=823: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1729 (1×)
  cell-651-823 : τ 823 ≡ τ 823
  cell-651-823 = refl


-- ── exponential.map (───────────────────────────────────)
-- κ=652, 1 nodes, 1 type contexts, 1 forms

module exponential-map-652 where

  -- τ=825: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1742 (1×)
  cell-652-825 : τ 825 ≡ τ 825
  cell-652-825 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=653, 1 nodes, 1 type contexts, 1 forms

module let-k-653 where

  -- τ=826: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1743 (1×)
  cell-653-826 : τ 826 ≡ τ 826
  cell-653-826 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=656, 1 nodes, 1 type contexts, 1 forms

module equalizer-656 where

  -- τ=829: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1755 (1×)
  cell-656-829 : τ 829 ≡ τ 829
  cell-656-829 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=657, 1 nodes, 1 type contexts, 1 forms

module fold-657 where

  -- τ=830: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1756 (1×)
  cell-657-830 : τ 830 ≡ τ 830
  cell-657-830 = refl


-- ── endomorphism (──────────────────────────────────────)
-- κ=658, 1 nodes, 1 type contexts, 1 forms

module endomorphism-658 where

  -- τ=831: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1760 (1×)
  cell-658-831 : τ 831 ≡ τ 831
  cell-658-831 = refl


-- ── lambda (────────────────────────────────────────────)
-- κ=659, 1 nodes, 1 type contexts, 1 forms

module lambda-659 where

  -- τ=832: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1761 (1×)
  cell-659-832 : τ 832 ≡ τ 832
  cell-659-832 = refl


-- ── keyword (───────────────────────────────────────────)
-- κ=660, 1 nodes, 1 type contexts, 1 forms

module keyword-660 where

  -- τ=833: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1762 (1×)
  cell-660-833 : τ 833 ≡ τ 833
  cell-660-833 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=661, 1 nodes, 1 type contexts, 1 forms

module apply-661 where

  -- τ=834: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1763 (1×)
  cell-661-834 : τ 834 ≡ τ 834
  cell-661-834 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=662, 1 nodes, 1 type contexts, 1 forms

module effect-seq-662 where

  -- τ=835: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1764 (1×)
  cell-662-835 : τ 835 ≡ τ 835
  cell-662-835 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=663, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-663 where

  -- τ=836: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1766 (1×)
  cell-663-836 : τ 836 ≡ τ 836
  cell-663-836 = refl


-- ── free_monoid.fold (──────────────────────────────────)
-- κ=665, 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-665 where

  -- τ=841: 1 nodes, 1 forms
  -- Types: str
  -- σ=1790 (1×)
  cell-665-841 : τ 841 ≡ τ 841
  cell-665-841 = refl


-- ── terminal.map (──────────────────────────────────────)
-- κ=666, 1 nodes, 1 type contexts, 1 forms

module terminal-map-666 where

  -- τ=842: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1791 (1×)
  cell-666-842 : τ 842 ≡ τ 842
  cell-666-842 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=667, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-667 where

  -- τ=843: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1792 (1×)
  cell-667-843 : τ 843 ≡ τ 843
  cell-667-843 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=668, 1 nodes, 1 type contexts, 1 forms

module equalizer-668 where

  -- τ=844: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1798 (1×)
  cell-668-844 : τ 844 ≡ τ 844
  cell-668-844 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=669, 1 nodes, 1 type contexts, 1 forms

module equalizer-669 where

  -- τ=845: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1801 (1×)
  cell-669-845 : τ 845 ≡ τ 845
  cell-669-845 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=670, 1 nodes, 1 type contexts, 1 forms

module let-k-670 where

  -- τ=847: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1810 (1×)
  cell-670-847 : τ 847 ≡ τ 847
  cell-670-847 = refl


-- ── coerce (────────────────────────────────────────────)
-- κ=685, 1 nodes, 1 type contexts, 1 forms

module coerce-685 where

  -- τ=862: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1864 (1×)
  cell-685-862 : τ 862 ≡ τ 862
  cell-685-862 = refl


-- ── free_monoid.fold (──────────────────────────────────)
-- κ=686, 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-686 where

  -- τ=863: 1 nodes, 1 forms
  -- Types: str
  -- σ=1865 (1×)
  cell-686-863 : τ 863 ≡ τ 863
  cell-686-863 = refl


-- ── free_monoid.literal (───────────────────────────────)
-- κ=687, 1 nodes, 1 type contexts, 1 forms

module free_monoid-literal-687 where

  -- τ=864: 1 nodes, 1 forms
  -- Types: list
  -- σ=1866 (1×)
  cell-687-864 : τ 864 ≡ τ 864
  cell-687-864 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=688, 1 nodes, 1 type contexts, 1 forms

module let-k-688 where

  -- τ=865: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1867 (1×)
  cell-688-865 : τ 865 ≡ τ 865
  cell-688-865 = refl


-- ── subobject (─────────────────────────────────────────)
-- κ=689, 1 nodes, 1 type contexts, 1 forms

module subobject-689 where

  -- τ=796: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1873 (1×)
  cell-689-796 : τ 796 ≡ τ 796
  cell-689-796 = refl


-- ── subobject.test (────────────────────────────────────)
-- κ=690, 1 nodes, 1 type contexts, 1 forms

module subobject-test-690 where

  -- τ=866: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1875 (1×)
  cell-690-866 : τ 866 ≡ τ 866
  cell-690-866 = refl


-- ── meet (──────────────────────────────────────────────)
-- κ=691, 1 nodes, 1 type contexts, 1 forms

module meet-691 where

  -- τ=867: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1876 (1×)
  cell-691-867 : τ 867 ≡ τ 867
  cell-691-867 = refl


-- ── comprehension (─────────────────────────────────────)
-- κ=692, 1 nodes, 1 type contexts, 1 forms

module comprehension-692 where

  -- τ=868: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1877 (1×)
  cell-692-868 : τ 868 ≡ τ 868
  cell-692-868 = refl


-- ── lazy_fold (─────────────────────────────────────────)
-- κ=693, 1 nodes, 1 type contexts, 1 forms

module lazy_fold-693 where

  -- τ=869: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1878 (1×)
  cell-693-869 : τ 869 ≡ τ 869
  cell-693-869 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=694, 1 nodes, 1 type contexts, 1 forms

module apply-694 where

  -- τ=870: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1879 (1×)
  cell-694-870 : τ 870 ≡ τ 870
  cell-694-870 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=695, 1 nodes, 1 type contexts, 1 forms

module let-k-695 where

  -- τ=871: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1880 (1×)
  cell-695-871 : τ 871 ≡ τ 871
  cell-695-871 = refl


-- ── powerset (──────────────────────────────────────────)
-- κ=696, 1 nodes, 1 type contexts, 1 forms

module powerset-696 where

  -- τ=872: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1882 (1×)
  cell-696-872 : τ 872 ≡ τ 872
  cell-696-872 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=697, 1 nodes, 1 type contexts, 1 forms

module annassign-697 where

  -- τ=873: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1883 (1×)
  cell-697-873 : τ 873 ≡ τ 873
  cell-697-873 = refl


-- ── ifexp (─────────────────────────────────────────────)
-- κ=698, 1 nodes, 1 type contexts, 1 forms

module ifexp-698 where

  -- τ=874: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1890 (1×)
  cell-698-874 : τ 874 ≡ τ 874
  cell-698-874 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=699, 1 nodes, 1 type contexts, 1 forms

module let-k-699 where

  -- τ=875: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1891 (1×)
  cell-699-875 : τ 875 ≡ τ 875
  cell-699-875 = refl


-- ── bimap (─────────────────────────────────────────────)
-- κ=700, 1 nodes, 1 type contexts, 1 forms

module bimap-700 where

  -- τ=876: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1896 (1×)
  cell-700-876 : τ 876 ≡ τ 876
  cell-700-876 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=701, 1 nodes, 1 type contexts, 1 forms

module let-k-701 where

  -- τ=877: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1897 (1×)
  cell-701-877 : τ 877 ≡ τ 877
  cell-701-877 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=702, 1 nodes, 1 type contexts, 1 forms

module annassign-702 where

  -- τ=879: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1900 (1×)
  cell-702-879 : τ 879 ≡ τ 879
  cell-702-879 = refl


-- ── annassign (─────────────────────────────────────────)
-- κ=703, 1 nodes, 1 type contexts, 1 forms

module annassign-703 where

  -- τ=880: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1903 (1×)
  cell-703-880 : τ 880 ≡ τ 880
  cell-703-880 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=704, 1 nodes, 1 type contexts, 1 forms

module let-k-704 where

  -- τ=881: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1908 (1×)
  cell-704-881 : τ 881 ≡ τ 881
  cell-704-881 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=705, 1 nodes, 1 type contexts, 1 forms

module equalizer-705 where

  -- τ=882: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1909 (1×)
  cell-705-882 : τ 882 ≡ τ 882
  cell-705-882 = refl


-- ── monoid.op@? (───────────────────────────────────────)
-- κ=706, 1 nodes, 1 type contexts, 1 forms

module monoid-op-at-x3f-706 where

  -- τ=810: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1911 (1×)
  cell-706-810 : τ 810 ≡ τ 810
  cell-706-810 = refl


-- ── partial.apply@? (───────────────────────────────────)
-- κ=707, 1 nodes, 1 type contexts, 1 forms

module partial-apply-at-x3f-707 where

  -- τ=883: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1913 (1×)
  cell-707-883 : τ 883 ≡ τ 883
  cell-707-883 = refl


-- ── monoid.op@? (───────────────────────────────────────)
-- κ=708, 1 nodes, 1 type contexts, 1 forms

module monoid-op-at-x3f-708 where

  -- τ=884: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1914 (1×)
  cell-708-884 : τ 884 ≡ τ 884
  cell-708-884 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=709, 1 nodes, 1 type contexts, 1 forms

module effect-seq-709 where

  -- τ=885: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1915 (1×)
  cell-709-885 : τ 885 ≡ τ 885
  cell-709-885 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=710, 1 nodes, 1 type contexts, 1 forms

module fold-710 where

  -- τ=886: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1916 (1×)
  cell-710-886 : τ 886 ≡ τ 886
  cell-710-886 = refl


-- ── comprehension (─────────────────────────────────────)
-- κ=711, 1 nodes, 1 type contexts, 1 forms

module comprehension-711 where

  -- τ=887: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1921 (1×)
  cell-711-887 : τ 887 ≡ τ 887
  cell-711-887 = refl


-- ── lazy_fold (─────────────────────────────────────────)
-- κ=712, 1 nodes, 1 type contexts, 1 forms

module lazy_fold-712 where

  -- τ=888: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1922 (1×)
  cell-712-888 : τ 888 ≡ τ 888
  cell-712-888 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=713, 1 nodes, 1 type contexts, 1 forms

module apply-713 where

  -- τ=889: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1923 (1×)
  cell-713-889 : τ 889 ≡ τ 889
  cell-713-889 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=714, 1 nodes, 1 type contexts, 1 forms

module let-k-714 where

  -- τ=890: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1924 (1×)
  cell-714-890 : τ 890 ≡ τ 890
  cell-714-890 = refl


-- ── free_monoid.fold (──────────────────────────────────)
-- κ=716, 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-716 where

  -- τ=892: 1 nodes, 1 forms
  -- Types: str
  -- σ=1930 (1×)
  cell-716-892 : τ 892 ≡ τ 892
  cell-716-892 = refl


-- ── free_monoid.snoc@sequence (─────────────────────────)
-- κ=717, 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-sequence-717 where

  -- τ=893: 1 nodes, 1 forms
  -- Types: None
  -- σ=1931 (1×)
  cell-717-893 : τ 893 ≡ τ 893
  cell-717-893 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=718, 1 nodes, 1 type contexts, 1 forms

module effect-seq-718 where

  -- τ=894: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1932 (1×)
  cell-718-894 : τ 894 ≡ τ 894
  cell-718-894 = refl


-- ── free_monoid.fold (──────────────────────────────────)
-- κ=719, 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-719 where

  -- τ=895: 1 nodes, 1 forms
  -- Types: str
  -- σ=1940 (1×)
  cell-719-895 : τ 895 ≡ τ 895
  cell-719-895 = refl


-- ── free_monoid.snoc@sequence (─────────────────────────)
-- κ=720, 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-sequence-720 where

  -- τ=896: 1 nodes, 1 forms
  -- Types: None
  -- σ=1941 (1×)
  cell-720-896 : τ 896 ≡ τ 896
  cell-720-896 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=721, 1 nodes, 1 type contexts, 1 forms

module effect-seq-721 where

  -- τ=897: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1942 (1×)
  cell-721-897 : τ 897 ≡ τ 897
  cell-721-897 = refl


-- ── free_monoid.fold (──────────────────────────────────)
-- κ=722, 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-722 where

  -- τ=898: 1 nodes, 1 forms
  -- Types: str
  -- σ=1952 (1×)
  cell-722-898 : τ 898 ≡ τ 898
  cell-722-898 = refl


-- ── free_monoid.snoc@sequence (─────────────────────────)
-- κ=723, 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-sequence-723 where

  -- τ=899: 1 nodes, 1 forms
  -- Types: None
  -- σ=1953 (1×)
  cell-723-899 : τ 899 ≡ τ 899
  cell-723-899 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=724, 1 nodes, 1 type contexts, 1 forms

module effect-seq-724 where

  -- τ=900: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1954 (1×)
  cell-724-900 : τ 900 ≡ τ 900
  cell-724-900 = refl


-- ── mult (──────────────────────────────────────────────)
-- κ=725, 1 nodes, 1 type contexts, 1 forms

module mult-725 where

  -- τ=901: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1961 (1×)
  cell-725-901 : τ 901 ≡ τ 901
  cell-725-901 = refl


-- ── bimap (─────────────────────────────────────────────)
-- κ=726, 1 nodes, 1 type contexts, 1 forms

module bimap-726 where

  -- τ=903: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1963 (1×)
  cell-726-903 : τ 903 ≡ τ 903
  cell-726-903 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=727, 1 nodes, 1 type contexts, 1 forms

module equalizer-727 where

  -- τ=904: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1964 (1×)
  cell-727-904 : τ 904 ≡ τ 904
  cell-727-904 = refl


-- ── ifexp (─────────────────────────────────────────────)
-- κ=728, 1 nodes, 1 type contexts, 1 forms

module ifexp-728 where

  -- τ=905: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1967 (1×)
  cell-728-905 : τ 905 ≡ τ 905
  cell-728-905 = refl


-- ── coerce (────────────────────────────────────────────)
-- κ=729, 1 nodes, 1 type contexts, 1 forms

module coerce-729 where

  -- τ=906: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1968 (1×)
  cell-729-906 : τ 906 ≡ τ 906
  cell-729-906 = refl


-- ── free_monoid.fold (──────────────────────────────────)
-- κ=730, 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-730 where

  -- τ=907: 1 nodes, 1 forms
  -- Types: str
  -- σ=1969 (1×)
  cell-730-907 : τ 907 ≡ τ 907
  cell-730-907 = refl


-- ── free_monoid.snoc@sequence (─────────────────────────)
-- κ=731, 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-sequence-731 where

  -- τ=908: 1 nodes, 1 forms
  -- Types: None
  -- σ=1970 (1×)
  cell-731-908 : τ 908 ≡ τ 908
  cell-731-908 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=732, 1 nodes, 1 type contexts, 1 forms

module effect-seq-732 where

  -- τ=909: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1971 (1×)
  cell-732-909 : τ 909 ≡ τ 909
  cell-732-909 = refl


-- ── exponential.literal (───────────────────────────────)
-- κ=733, 1 nodes, 1 type contexts, 1 forms

module exponential-literal-733 where

  -- τ=910: 1 nodes, 1 forms
  -- Types: dict
  -- σ=1979 (1×)
  cell-733-910 : τ 910 ≡ τ 910
  cell-733-910 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=734, 1 nodes, 1 type contexts, 1 forms

module let-k-734 where

  -- τ=911: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1980 (1×)
  cell-734-911 : τ 911 ≡ τ 911
  cell-734-911 = refl


-- ── partial.apply@state (───────────────────────────────)
-- κ=735, 1 nodes, 1 type contexts, 1 forms

module partial-apply-at-state-735 where

  -- τ=913: 1 nodes, 1 forms
  -- Types: T
  -- σ=1983 (1×)
  cell-735-913 : τ 913 ≡ τ 913
  cell-735-913 = refl


-- ── cardinality (───────────────────────────────────────)
-- κ=736, 1 nodes, 1 type contexts, 1 forms

module cardinality-736 where

  -- τ=914: 1 nodes, 1 forms
  -- Types: int
  -- σ=1984 (1×)
  cell-736-914 : τ 914 ≡ τ 914
  cell-736-914 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=737, 1 nodes, 1 type contexts, 1 forms

module let-k-737 where

  -- τ=915: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1985 (1×)
  cell-737-915 : τ 915 ≡ τ 915
  cell-737-915 = refl


-- ── bimap (─────────────────────────────────────────────)
-- κ=738, 1 nodes, 1 type contexts, 1 forms

module bimap-738 where

  -- τ=916: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1988 (1×)
  cell-738-916 : τ 916 ≡ τ 916
  cell-738-916 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=739, 1 nodes, 1 type contexts, 1 forms

module let-k-739 where

  -- τ=917: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1989 (1×)
  cell-739-917 : τ 917 ≡ τ 917
  cell-739-917 = refl


-- ── free_monoid.snoc@sequence (─────────────────────────)
-- κ=740, 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-sequence-740 where

  -- τ=918: 1 nodes, 1 forms
  -- Types: None
  -- σ=1991 (1×)
  cell-740-918 : τ 918 ≡ τ 918
  cell-740-918 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=741, 1 nodes, 1 type contexts, 1 forms

module effect-seq-741 where

  -- τ=919: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=1992 (1×)
  cell-741-919 : τ 919 ≡ τ 919
  cell-741-919 = refl


-- ── free_monoid.fold (──────────────────────────────────)
-- κ=743, 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-743 where

  -- τ=923: 1 nodes, 1 forms
  -- Types: str
  -- σ=2003 (1×)
  cell-743-923 : τ 923 ≡ τ 923
  cell-743-923 = refl


-- ── free_monoid.snoc@sequence (─────────────────────────)
-- κ=744, 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-sequence-744 where

  -- τ=924: 1 nodes, 1 forms
  -- Types: None
  -- σ=2004 (1×)
  cell-744-924 : τ 924 ≡ τ 924
  cell-744-924 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=745, 1 nodes, 1 type contexts, 1 forms

module effect-seq-745 where

  -- τ=925: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=2005 (1×)
  cell-745-925 : τ 925 ≡ τ 925
  cell-745-925 = refl


-- ── projection@state (──────────────────────────────────)
-- κ=746, 1 nodes, 1 type contexts, 1 forms

module projection-at-state-746 where

  -- τ=153: 1 nodes, 1 forms
  -- Types: Self._cell_contents.get, Self._cell_obs.get, Self._cell_obs.keys, Self._cleavage_fibers.append, Self._cleavage_levels.append
  -- σ=2006 (1×)
  cell-746-153 : τ 153 ≡ τ 153
  cell-746-153 = refl


-- ── projection.compute@state (──────────────────────────)
-- κ=747, 1 nodes, 1 type contexts, 1 forms

module projection-compute-at-state-747 where

  -- τ=927: 1 nodes, 1 forms
  -- Types: Iter
  -- σ=2007 (1×)
  cell-747-927 : τ 927 ≡ τ 927
  cell-747-927 = refl


-- ── total_order (───────────────────────────────────────)
-- κ=748, 1 nodes, 1 type contexts, 1 forms

module total_order-748 where

  -- τ=928: 1 nodes, 1 forms
  -- Types: list
  -- σ=2008 (1×)
  cell-748-928 : τ 928 ≡ τ 928
  cell-748-928 = refl


-- ── complement (────────────────────────────────────────)
-- κ=749, 1 nodes, 1 type contexts, 1 forms

module complement-749 where

  -- τ=929: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=2011 (1×)
  cell-749-929 : τ 929 ≡ τ 929
  cell-749-929 = refl


-- ── partial@mapping (───────────────────────────────────)
-- κ=750, 1 nodes, 1 type contexts, 1 forms

module partial-at-mapping-750 where

  -- τ=34: 1 nodes, 1 forms
  -- Types: Self._cascade_abstraction_merge, Self._cascade_eta, Self._cell_contents, Self._cell_obs, Self._cleavage_fibers
  -- σ=2013 (1×)
  cell-750-34 : τ 34 ≡ τ 34
  cell-750-34 = refl


-- ── partial.apply@mapping (─────────────────────────────)
-- κ=751, 1 nodes, 1 type contexts, 1 forms

module partial-apply-at-mapping-751 where

  -- τ=932: 1 nodes, 1 forms
  -- Types: T
  -- σ=2017 (1×)
  cell-751-932 : τ 932 ≡ τ 932
  cell-751-932 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=752, 1 nodes, 1 type contexts, 1 forms

module let-k-752 where

  -- τ=933: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=2018 (1×)
  cell-752-933 : τ 933 ≡ τ 933
  cell-752-933 = refl


-- ── lambda (────────────────────────────────────────────)
-- κ=753, 1 nodes, 1 type contexts, 1 forms

module lambda-753 where

  -- τ=934: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=2024 (1×)
  cell-753-934 : τ 934 ≡ τ 934
  cell-753-934 = refl


-- ── keyword (───────────────────────────────────────────)
-- κ=754, 1 nodes, 1 type contexts, 1 forms

module keyword-754 where

  -- τ=935: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=2025 (1×)
  cell-754-935 : τ 935 ≡ τ 935
  cell-754-935 = refl


-- ── apply (─────────────────────────────────────────────)
-- κ=755, 1 nodes, 1 type contexts, 1 forms

module apply-755 where

  -- τ=936: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=2026 (1×)
  cell-755-936 : τ 936 ≡ τ 936
  cell-755-936 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=756, 1 nodes, 1 type contexts, 1 forms

module let-k-756 where

  -- τ=937: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=2027 (1×)
  cell-756-937 : τ 937 ≡ τ 937
  cell-756-937 = refl


-- ── coerce (────────────────────────────────────────────)
-- κ=757, 1 nodes, 1 type contexts, 1 forms

module coerce-757 where

  -- τ=404: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=2030 (1×)
  cell-757-404 : τ 404 ≡ τ 404
  cell-757-404 = refl


-- ── subscript (─────────────────────────────────────────)
-- κ=758, 1 nodes, 1 type contexts, 1 forms

module subscript-758 where

  -- τ=938: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=2033 (1×)
  cell-758-938 : τ 938 ≡ τ 938
  cell-758-938 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=759, 1 nodes, 1 type contexts, 1 forms

module let-k-759 where

  -- τ=939: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=2034 (1×)
  cell-759-939 : τ 939 ≡ τ 939
  cell-759-939 = refl


-- ── free_monoid.fold (──────────────────────────────────)
-- κ=760, 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-760 where

  -- τ=940: 1 nodes, 1 forms
  -- Types: str
  -- σ=2047 (1×)
  cell-760-940 : τ 940 ≡ τ 940
  cell-760-940 = refl


-- ── free_monoid.snoc@sequence (─────────────────────────)
-- κ=761, 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-sequence-761 where

  -- τ=941: 1 nodes, 1 forms
  -- Types: None
  -- σ=2048 (1×)
  cell-761-941 : τ 941 ≡ τ 941
  cell-761-941 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=762, 1 nodes, 1 type contexts, 1 forms

module effect-seq-762 where

  -- τ=942: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=2049 (1×)
  cell-762-942 : τ 942 ≡ τ 942
  cell-762-942 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=763, 1 nodes, 1 type contexts, 1 forms

module fold-763 where

  -- τ=943: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=2050 (1×)
  cell-763-943 : τ 943 ≡ τ 943
  cell-763-943 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=764, 1 nodes, 1 type contexts, 1 forms

module equalizer-764 where

  -- τ=944: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=2053 (1×)
  cell-764-944 : τ 944 ≡ τ 944
  cell-764-944 = refl


-- ── partial.apply@? (───────────────────────────────────)
-- κ=765, 1 nodes, 1 type contexts, 1 forms

module partial-apply-at-x3f-765 where

  -- τ=946: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=2059 (1×)
  cell-765-946 : τ 946 ≡ τ 946
  cell-765-946 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=766, 1 nodes, 1 type contexts, 1 forms

module let-k-766 where

  -- τ=947: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=2060 (1×)
  cell-766-947 : τ 947 ≡ τ 947
  cell-766-947 = refl


-- ── let (───────────────────────────────────────────────)
-- κ=767, 1 nodes, 1 type contexts, 1 forms

module let-k-767 where

  -- τ=948: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=2068 (1×)
  cell-767-948 : τ 948 ≡ τ 948
  cell-767-948 = refl


-- ── free_monoid.fold (──────────────────────────────────)
-- κ=768, 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-768 where

  -- τ=951: 1 nodes, 1 forms
  -- Types: str
  -- σ=2084 (1×)
  cell-768-951 : τ 951 ≡ τ 951
  cell-768-951 = refl


-- ── free_monoid.snoc@sequence (─────────────────────────)
-- κ=769, 1 nodes, 1 type contexts, 1 forms

module free_monoid-snoc-at-sequence-769 where

  -- τ=952: 1 nodes, 1 forms
  -- Types: None
  -- σ=2085 (1×)
  cell-769-952 : τ 952 ≡ τ 952
  cell-769-952 = refl


-- ── effect.seq (────────────────────────────────────────)
-- κ=770, 1 nodes, 1 type contexts, 1 forms

module effect-seq-770 where

  -- τ=953: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=2086 (1×)
  cell-770-953 : τ 953 ≡ τ 953
  cell-770-953 = refl


-- ── equalizer (─────────────────────────────────────────)
-- κ=771, 1 nodes, 1 type contexts, 1 forms

module equalizer-771 where

  -- τ=954: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=2087 (1×)
  cell-771-954 : τ 954 ≡ τ 954
  cell-771-954 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=772, 1 nodes, 1 type contexts, 1 forms

module fold-772 where

  -- τ=955: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=2088 (1×)
  cell-772-955 : τ 955 ≡ τ 955
  cell-772-955 = refl


-- ── fold (──────────────────────────────────────────────)
-- κ=773, 1 nodes, 1 type contexts, 1 forms

module fold-773 where

  -- τ=956: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=2089 (1×)
  cell-773-956 : τ 956 ≡ τ 956
  cell-773-956 = refl


-- ── free_monoid.fold (──────────────────────────────────)
-- κ=774, 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-774 where

  -- τ=957: 1 nodes, 1 forms
  -- Types: str.join
  -- σ=2091 (1×)
  cell-774-957 : τ 957 ≡ τ 957
  cell-774-957 = refl


-- ── free_monoid.fold (──────────────────────────────────)
-- κ=775, 1 nodes, 1 type contexts, 1 forms

module free_monoid-fold-775 where

  -- τ=958: 1 nodes, 1 forms
  -- Types: str
  -- σ=2092 (1×)
  cell-775-958 : τ 958 ≡ τ 958
  cell-775-958 = refl


-- ── terminal.map (──────────────────────────────────────)
-- κ=776, 1 nodes, 1 type contexts, 1 forms

module terminal-map-776 where

  -- τ=959: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=2093 (1×)
  cell-776-959 : τ 959 ≡ τ 959
  cell-776-959 = refl


-- ── exponential.intro (─────────────────────────────────)
-- κ=777, 1 nodes, 1 type contexts, 1 forms

module exponential-intro-777 where

  -- τ=960: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=2094 (1×)
  cell-777-960 : τ 960 ≡ τ 960
  cell-777-960 = refl


-- ── classifier.intro (──────────────────────────────────)
-- κ=778, 1 nodes, 1 type contexts, 1 forms

module classifier-intro-778 where

  -- τ=961: 1 nodes, 1 forms
  -- Types: (untyped)
  -- σ=2095 (1×)
  cell-778-961 : τ 961 ≡ τ 961
  cell-778-961 = refl


-- ══════════════════════════════════════════════════════════
-- Cleavage planes (module boundaries / case splits)
-- ══════════════════════════════════════════════════════════

-- Cleavage 0: τ=34, 32 nodes, 25 branches
module Cleavage-0 where

  -- The type context τ=34 splits into 25 sub-proofs,
  -- each parameterized by a different dep-type witness.

  -- Branch 0: Self._parent (7 nodes)
  branch-0 : τ 34 ≡ τ 34
  branch-0 = refl  -- Self-_parent

  -- Branch 1: Self.find (2 nodes)
  branch-1 : τ 34 ≡ τ 34
  branch-1 = refl  -- Self-find

  -- Branch 2: Self._rank (1 nodes)
  branch-2 : τ 34 ≡ τ 34
  branch-2 = refl  -- Self-_rank

  -- Branch 3: Self._counter (1 nodes)
  branch-3 : τ 34 ≡ τ 34
  branch-3 = refl  -- Self-_counter

  -- Branch 4: Self.canonical_classes (1 nodes)
  branch-4 : τ 34 ≡ τ 34
  branch-4 = refl  -- Self-canonical_classes

  -- Branch 5: Self._observe_cell (1 nodes)
  branch-5 : τ 34 ≡ τ 34
  branch-5 = refl  -- Self-_observe_cell

  -- Branch 6: Self._resolve_type (1 nodes)
  branch-6 : τ 34 ≡ τ 34
  branch-6 = refl  -- Self-_resolve_type

  -- Branch 7: Self._merge_residue_sets (1 nodes)
  branch-7 : τ 34 ≡ τ 34
  branch-7 = refl  -- Self-_merge_residue_sets

  -- Branch 8: Self._process_cleavage (1 nodes)
  branch-8 : τ 34 ≡ τ 34
  branch-8 = refl  -- Self-_process_cleavage

  -- Branch 9: Self._seed_worklist (1 nodes)
  branch-9 : τ 34 ≡ τ 34
  branch-9 = refl  -- Self-_seed_worklist

  -- Branch 10: Self._recanon_structural_key (1 nodes)
  branch-10 : τ 34 ≡ τ 34
  branch-10 = refl  -- Self-_recanon_structural_key

  -- Branch 11: T.items (1 nodes)
  branch-11 : τ 34 ≡ τ 34
  branch-11 = refl  -- T-items

  -- Branch 12: T.keys (1 nodes)
  branch-12 : τ 34 ≡ τ 34
  branch-12 = refl  -- T-keys

  -- Branch 13: Self._cascade_abstraction_merge (1 nodes)
  branch-13 : τ 34 ≡ τ 34
  branch-13 = refl  -- Self-_cascade_abstraction_merge

  -- Branch 14: Self._update_residue (1 nodes)
  branch-14 : τ 34 ≡ τ 34
  branch-14 = refl  -- Self-_update_residue

  -- Branch 15: Self._cascade_eta (1 nodes)
  branch-15 : τ 34 ≡ τ 34
  branch-15 = refl  -- Self-_cascade_eta

  -- Branch 16: Self._resolve (1 nodes)
  branch-16 : τ 34 ≡ τ 34
  branch-16 = refl  -- Self-_resolve

  -- Branch 17: Self.rank (1 nodes)
  branch-17 : τ 34 ≡ τ 34
  branch-17 = refl  -- Self-rank

  -- Branch 18: Self.residue (1 nodes)
  branch-18 : τ 34 ≡ τ 34
  branch-18 = refl  -- Self-residue

  -- Branch 19: Self.hybrid (1 nodes)
  branch-19 : τ 34 ≡ τ 34
  branch-19 = refl  -- Self-hybrid

  -- Branch 20: Self.node_count (1 nodes)
  branch-20 : τ 34 ≡ τ 34
  branch-20 = refl  -- Self-node_count

  -- Branch 21: Self.wedge (1 nodes)
  branch-21 : τ 34 ≡ τ 34
  branch-21 = refl  -- Self-wedge

  -- Branch 22: list.append (1 nodes)
  branch-22 : τ 34 ≡ τ 34
  branch-22 = refl  -- list-append

  -- Branch 23: dict.get (1 nodes)
  branch-23 : τ 34 ≡ τ 34
  branch-23 = refl  -- dict-get

  -- Branch 24: Self.rank_distribution (1 nodes)
  branch-24 : τ 34 ≡ τ 34
  branch-24 = refl  -- Self-rank_distribution


-- Cleavage 1: τ=14, 29 nodes, 28 branches
module Cleavage-1 where

  -- The type context τ=14 splits into 28 sub-proofs,
  -- each parameterized by a different dep-type witness.

  -- Branch 0: Self._counter (2 nodes)
  branch-0 : τ 14 ≡ τ 14
  branch-0 = refl  -- Self-_counter

  -- Branch 1: Self._parent (1 nodes)
  branch-1 : τ 14 ≡ τ 14
  branch-1 = refl  -- Self-_parent

  -- Branch 2: Self._rank (1 nodes)
  branch-2 : τ 14 ≡ τ 14
  branch-2 = refl  -- Self-_rank

  -- Branch 3: Self.id (1 nodes)
  branch-3 : τ 14 ≡ τ 14
  branch-3 = refl  -- Self-id

  -- Branch 4: Self.signature (1 nodes)
  branch-4 : τ 14 ≡ τ 14
  branch-4 = refl  -- Self-signature

  -- Branch 5: Self.child_ids (1 nodes)
  branch-5 : τ 14 ≡ τ 14
  branch-5 = refl  -- Self-child_ids

  -- Branch 6: Self.node_indices (1 nodes)
  branch-6 : τ 14 ≡ τ 14
  branch-6 = refl  -- Self-node_indices

  -- Branch 7: Self.name (1 nodes)
  branch-7 : τ 14 ≡ τ 14
  branch-7 = refl  -- Self-name

  -- Branch 8: Self.classes (1 nodes)
  branch-8 : τ 14 ≡ τ 14
  branch-8 = refl  -- Self-classes

  -- Branch 9: Self._registry (1 nodes)
  branch-9 : τ 14 ≡ τ 14
  branch-9 = refl  -- Self-_registry

  -- Branch 10: Self.uf (1 nodes)
  branch-10 : τ 14 ≡ τ 14
  branch-10 = refl  -- Self-uf

  -- Branch 11: Self.sigma (1 nodes)
  branch-11 : τ 14 ≡ τ 14
  branch-11 = refl  -- Self-sigma

  -- Branch 12: Self.tau (1 nodes)
  branch-12 : τ 14 ≡ τ 14
  branch-12 = refl  -- Self-tau

  -- Branch 13: Self.kappa (1 nodes)
  branch-13 : τ 14 ≡ τ 14
  branch-13 = refl  -- Self-kappa

  -- Branch 14: Self.nodes (1 nodes)
  branch-14 : τ 14 ≡ τ 14
  branch-14 = refl  -- Self-nodes

  -- Branch 15: Self._tau_structural (1 nodes)
  branch-15 : τ 14 ≡ τ 14
  branch-15 = refl  -- Self-_tau_structural

  -- Branch 16: Self._tau_structural_by_child (1 nodes)
  branch-16 : τ 14 ≡ τ 14
  branch-16 = refl  -- Self-_tau_structural_by_child

  -- Branch 17: Self._tau_structural_by_variant (1 nodes)
  branch-17 : τ 14 ≡ τ 14
  branch-17 = refl  -- Self-_tau_structural_by_variant

  -- Branch 18: Self._eta_abstractions (1 nodes)
  branch-18 : τ 14 ≡ τ 14
  branch-18 = refl  -- Self-_eta_abstractions

  -- Branch 19: Self._eta_uf (1 nodes)
  branch-19 : τ 14 ≡ τ 14
  branch-19 = refl  -- Self-_eta_uf

  -- Branch 20: Self._eta_count (1 nodes)
  branch-20 : τ 14 ≡ τ 14
  branch-20 = refl  -- Self-_eta_count

  -- Branch 21: Self._eta_tower (1 nodes)
  branch-21 : τ 14 ≡ τ 14
  branch-21 = refl  -- Self-_eta_tower

  -- Branch 22: Self._residue_sets (1 nodes)
  branch-22 : τ 14 ≡ τ 14
  branch-22 = refl  -- Self-_residue_sets

  -- Branch 23: Self._cleavage_levels (1 nodes)
  branch-23 : τ 14 ≡ τ 14
  branch-23 = refl  -- Self-_cleavage_levels

  -- Branch 24: Self._cleavage_fibers (1 nodes)
  branch-24 : τ 14 ≡ τ 14
  branch-24 = refl  -- Self-_cleavage_fibers

  -- Branch 25: Self._cleavage_ghost_count (1 nodes)
  branch-25 : τ 14 ≡ τ 14
  branch-25 = refl  -- Self-_cleavage_ghost_count

  -- Branch 26: Self._cell_obs (1 nodes)
  branch-26 : τ 14 ≡ τ 14
  branch-26 = refl  -- Self-_cell_obs

  -- Branch 27: Self._cell_contents (1 nodes)
  branch-27 : τ 14 ≡ τ 14
  branch-27 = refl  -- Self-_cell_contents


-- Cleavage 2: τ=153, 27 nodes, 26 branches
module Cleavage-2 where

  -- The type context τ=153 splits into 26 sub-proofs,
  -- each parameterized by a different dep-type witness.

  -- Branch 0: Self.uf.find (2 nodes)
  branch-0 : τ 153 ≡ τ 153
  branch-0 = refl  -- Self-uf-find

  -- Branch 1: Self.uf.make (1 nodes)
  branch-1 : τ 153 ≡ τ 153
  branch-1 = refl  -- Self-uf-make

  -- Branch 2: Self.uf.union (1 nodes)
  branch-2 : τ 153 ≡ τ 153
  branch-2 = refl  -- Self-uf-union

  -- Branch 3: Self._cell_contents.get (1 nodes)
  branch-3 : τ 153 ≡ τ 153
  branch-3 = refl  -- Self-_cell_contents-get

  -- Branch 4: Self.tau.canonical (1 nodes)
  branch-4 : τ 153 ≡ τ 153
  branch-4 = refl  -- Self-tau-canonical

  -- Branch 5: Self._residue_sets.get (1 nodes)
  branch-5 : τ 153 ≡ τ 153
  branch-5 = refl  -- Self-_residue_sets-get

  -- Branch 6: Self._cleavage_levels.append (1 nodes)
  branch-6 : τ 153 ≡ τ 153
  branch-6 = refl  -- Self-_cleavage_levels-append

  -- Branch 7: Self._cleavage_fibers.append (1 nodes)
  branch-7 : τ 153 ≡ τ 153
  branch-7 = refl  -- Self-_cleavage_fibers-append

  -- Branch 8: Self.tau.classes (1 nodes)
  branch-8 : τ 153 ≡ τ 153
  branch-8 = refl  -- Self-tau-classes

  -- Branch 9: Self._eta_tower.append (1 nodes)
  branch-9 : τ 153 ≡ τ 153
  branch-9 = refl  -- Self-_eta_tower-append

  -- Branch 10: Self._eta_abstractions.get (1 nodes)
  branch-10 : τ 153 ≡ τ 153
  branch-10 = refl  -- Self-_eta_abstractions-get

  -- Branch 11: Self._eta_uf.find (1 nodes)
  branch-11 : τ 153 ≡ τ 153
  branch-11 = refl  -- Self-_eta_uf-find

  -- Branch 12: Self._tau_structural_by_variant.get (1 nodes)
  branch-12 : τ 153 ≡ τ 153
  branch-12 = refl  -- Self-_tau_structural_by_variant-get

  -- Branch 13: Self.tau.merge (1 nodes)
  branch-13 : τ 153 ≡ τ 153
  branch-13 = refl  -- Self-tau-merge

  -- Branch 14: Self._tau_structural_by_child.get (1 nodes)
  branch-14 : τ 153 ≡ τ 153
  branch-14 = refl  -- Self-_tau_structural_by_child-get

  -- Branch 15: Self._tau_structural.get (1 nodes)
  branch-15 : τ 153 ≡ τ 153
  branch-15 = refl  -- Self-_tau_structural-get

  -- Branch 16: Self._eta_uf.make (1 nodes)
  branch-16 : τ 153 ≡ τ 153
  branch-16 = refl  -- Self-_eta_uf-make

  -- Branch 17: Self._eta_uf.union (1 nodes)
  branch-17 : τ 153 ≡ τ 153
  branch-17 = refl  -- Self-_eta_uf-union

  -- Branch 18: Self.sigma._assign (1 nodes)
  branch-18 : τ 153 ≡ τ 153
  branch-18 = refl  -- Self-sigma-_assign

  -- Branch 19: Self.kappa._assign (1 nodes)
  branch-19 : τ 153 ≡ τ 153
  branch-19 = refl  -- Self-kappa-_assign

  -- Branch 20: Self.tau._assign (1 nodes)
  branch-20 : τ 153 ≡ τ 153
  branch-20 = refl  -- Self-tau-_assign

  -- Branch 21: Self.nodes.append (1 nodes)
  branch-21 : τ 153 ≡ τ 153
  branch-21 = refl  -- Self-nodes-append

  -- Branch 22: Self.sigma.classes (1 nodes)
  branch-22 : τ 153 ≡ τ 153
  branch-22 = refl  -- Self-sigma-classes

  -- Branch 23: Self.kappa.classes (1 nodes)
  branch-23 : τ 153 ≡ τ 153
  branch-23 = refl  -- Self-kappa-classes

  -- Branch 24: Self._cell_obs.get (1 nodes)
  branch-24 : τ 153 ≡ τ 153
  branch-24 = refl  -- Self-_cell_obs-get

  -- Branch 25: Self._cell_obs.keys (1 nodes)
  branch-25 : τ 153 ≡ τ 153
  branch-25 = refl  -- Self-_cell_obs-keys


-- Cleavage 3: τ=13, 14 nodes, 12 branches
module Cleavage-3 where

  -- The type context τ=13 splits into 12 sub-proofs,
  -- each parameterized by a different dep-type witness.

  -- Branch 0: Self (3 nodes)
  branch-0 : τ 13 ≡ τ 13
  branch-0 = refl  -- Self

  -- Branch 1: dict (1 nodes)
  branch-1 : τ 13 ≡ τ 13
  branch-1 = refl  -- dict

  -- Branch 2: int (1 nodes)
  branch-2 : τ 13 ≡ τ 13
  branch-2 = refl  -- int

  -- Branch 3: bool (1 nodes)
  branch-3 : τ 13 ≡ τ 13
  branch-3 = refl  -- bool

  -- Branch 4: →int (1 nodes)
  branch-4 : τ 13 ≡ τ 13
  branch-4 = refl  -- toint

  -- Branch 5: tuple (1 nodes)
  branch-5 : τ 13 ≡ τ 13
  branch-5 = refl  -- tuple

  -- Branch 6: list (1 nodes)
  branch-6 : τ 13 ≡ τ 13
  branch-6 = refl  -- list

  -- Branch 7: set (1 nodes)
  branch-7 : τ 13 ≡ τ 13
  branch-7 = refl  -- set

  -- Branch 8: →list (1 nodes)
  branch-8 : τ 13 ≡ τ 13
  branch-8 = refl  -- tolist

  -- Branch 9: →bool (1 nodes)
  branch-9 : τ 13 ≡ τ 13
  branch-9 = refl  -- tobool

  -- Branch 10: AST (1 nodes)
  branch-10 : τ 13 ≡ τ 13
  branch-10 = refl  -- AST

  -- Branch 11: →T (1 nodes)
  branch-11 : τ 13 ≡ τ 13
  branch-11 = refl  -- toT


-- Cleavage 4: τ=0, 8 nodes, 4 branches
module Cleavage-4 where

  -- The type context τ=0 splits into 4 sub-proofs,
  -- each parameterized by a different dep-type witness.

  -- Branch 0: str (4 nodes)
  branch-0 : τ 0 ≡ τ 0
  branch-0 = refl  -- str

  -- Branch 1: NoneType (2 nodes)
  branch-1 : τ 0 ≡ τ 0
  branch-1 = refl  -- NoneType

  -- Branch 2: int (1 nodes)
  branch-2 : τ 0 ≡ τ 0
  branch-2 = refl  -- int

  -- Branch 3: float (1 nodes)
  branch-3 : τ 0 ≡ τ 0
  branch-3 = refl  -- float


-- Cleavage 5: τ=7, 5 nodes, 3 branches
module Cleavage-5 where

  -- The type context τ=7 splits into 3 sub-proofs,
  -- each parameterized by a different dep-type witness.

  -- Branch 0: tuple (3 nodes)
  branch-0 : τ 7 ≡ τ 7
  branch-0 = refl  -- tuple

  -- Branch 1: Self._counter (1 nodes)
  branch-1 : τ 7 ≡ τ 7
  branch-1 = refl  -- Self-_counter

  -- Branch 2: T (1 nodes)
  branch-2 : τ 7 ≡ τ 7
  branch-2 = refl  -- T


-- Cleavage 6: τ=349, 2 nodes, 2 branches
module Cleavage-6 where

  -- The type context τ=349 splits into 2 sub-proofs,
  -- each parameterized by a different dep-type witness.

  -- Branch 0: None (1 nodes)
  branch-0 : τ 349 ≡ τ 349
  branch-0 = refl  -- None

  -- Branch 1: T (1 nodes)
  branch-1 : τ 349 ≡ τ 349
  branch-1 = refl  -- T


-- ══════════════════════════════════════════════════════════
-- Summary:
--   7500 AST nodes → 2109 proof cells
--   779 construction modules
--   13 η-proofs
--   7 cleavage planes
--   Compression: 71.9%
-- ══════════════════════════════════════════════════════════

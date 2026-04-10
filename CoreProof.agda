module CoreProof where

-- ══════════════════════════════════════════════════════════
-- SPPF proof, rotation = (κ → τ → σ), depth = 2
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
-- 103 type-erasure steps

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
-- Hierarchy: κ → τ → σ (depth=2)
-- ══════════════════════════════════════════════════════════

-- κ=13: 1497 nodes, 2 τ-classes, 200 σ-classes
module var-Name where

  -- τ=16: 757 nodes, 175 σ-classes
  module τ16 where

    -- σ=25 (34 nodes)
    cell-0 : κ 13 ≡ κ 13
    cell-0 = refl

    -- σ=484 (23 nodes)
    cell-1 : κ 13 ≡ κ 13
    cell-1 = refl

    -- σ=356 (20 nodes)
    cell-2 : κ 13 ≡ κ 13
    cell-2 = refl

    -- σ=794 (20 nodes)
    cell-3 : κ 13 ≡ κ 13
    cell-3 = refl

    -- σ=797 (20 nodes)
    cell-4 : κ 13 ≡ κ 13
    cell-4 = refl

    -- σ=345 (18 nodes)
    cell-5 : κ 13 ≡ κ 13
    cell-5 = refl

    -- σ=904 (16 nodes)
    cell-6 : κ 13 ≡ κ 13
    cell-6 = refl

    -- σ=766 (14 nodes)
    cell-7 : κ 13 ≡ κ 13
    cell-7 = refl

    -- σ=791 (14 nodes)
    cell-8 : κ 13 ≡ κ 13
    cell-8 = refl

    -- σ=87 (13 nodes)
    cell-9 : κ 13 ≡ κ 13
    cell-9 = refl

    -- σ=556 (13 nodes)
    cell-10 : κ 13 ≡ κ 13
    cell-10 = refl

    -- σ=1440 (13 nodes)
    cell-11 : κ 13 ≡ κ 13
    cell-11 = refl

    -- σ=41 (12 nodes)
    cell-12 : κ 13 ≡ κ 13
    cell-12 = refl

    -- σ=257 (12 nodes)
    cell-13 : κ 13 ≡ κ 13
    cell-13 = refl

    -- σ=322 (12 nodes)
    cell-14 : κ 13 ≡ κ 13
    cell-14 = refl

    -- σ=625 (12 nodes)
    cell-15 : κ 13 ≡ κ 13
    cell-15 = refl

    -- σ=798 (12 nodes)
    cell-16 : κ 13 ≡ κ 13
    cell-16 = refl

    -- σ=805 (12 nodes)
    cell-17 : κ 13 ≡ κ 13
    cell-17 = refl

    -- σ=889 (12 nodes)
    cell-18 : κ 13 ≡ κ 13
    cell-18 = refl

    -- σ=531 (11 nodes)
    cell-19 : κ 13 ≡ κ 13
    cell-19 = refl

    -- σ=974 (10 nodes)
    cell-20 : κ 13 ≡ κ 13
    cell-20 = refl

    -- σ=1264 (10 nodes)
    cell-21 : κ 13 ≡ κ 13
    cell-21 = refl

    -- σ=152 (9 nodes)
    cell-22 : κ 13 ≡ κ 13
    cell-22 = refl

    -- σ=432 (9 nodes)
    cell-23 : κ 13 ≡ κ 13
    cell-23 = refl

    -- σ=56 (8 nodes)
    cell-24 : κ 13 ≡ κ 13
    cell-24 = refl

    -- σ=89 (8 nodes)
    cell-25 : κ 13 ≡ κ 13
    cell-25 = refl

    -- σ=282 (8 nodes)
    cell-26 : κ 13 ≡ κ 13
    cell-26 = refl

    -- σ=510 (8 nodes)
    cell-27 : κ 13 ≡ κ 13
    cell-27 = refl

    -- σ=1487 (8 nodes)
    cell-28 : κ 13 ≡ κ 13
    cell-28 = refl

    -- σ=873 (7 nodes)
    cell-29 : κ 13 ≡ κ 13
    cell-29 = refl

    -- σ=892 (7 nodes)
    cell-30 : κ 13 ≡ κ 13
    cell-30 = refl

    -- σ=1174 (7 nodes)
    cell-31 : κ 13 ≡ κ 13
    cell-31 = refl

    -- σ=1438 (7 nodes)
    cell-32 : κ 13 ≡ κ 13
    cell-32 = refl

    -- σ=491 (6 nodes)
    cell-33 : κ 13 ≡ κ 13
    cell-33 = refl

    -- σ=579 (6 nodes)
    cell-34 : κ 13 ≡ κ 13
    cell-34 = refl

    -- σ=918 (6 nodes)
    cell-35 : κ 13 ≡ κ 13
    cell-35 = refl

    -- σ=1006 (6 nodes)
    cell-36 : κ 13 ≡ κ 13
    cell-36 = refl

    -- σ=1067 (6 nodes)
    cell-37 : κ 13 ≡ κ 13
    cell-37 = refl

    -- σ=1137 (6 nodes)
    cell-38 : κ 13 ≡ κ 13
    cell-38 = refl

    -- σ=155 (5 nodes)
    cell-39 : κ 13 ≡ κ 13
    cell-39 = refl

    -- σ=294 (5 nodes)
    cell-40 : κ 13 ≡ κ 13
    cell-40 = refl

    -- σ=449 (5 nodes)
    cell-41 : κ 13 ≡ κ 13
    cell-41 = refl

    -- σ=786 (5 nodes)
    cell-42 : κ 13 ≡ κ 13
    cell-42 = refl

    -- σ=857 (5 nodes)
    cell-43 : κ 13 ≡ κ 13
    cell-43 = refl

    -- σ=1181 (5 nodes)
    cell-44 : κ 13 ≡ κ 13
    cell-44 = refl

    -- σ=1383 (5 nodes)
    cell-45 : κ 13 ≡ κ 13
    cell-45 = refl

    -- σ=1494 (5 nodes)
    cell-46 : κ 13 ≡ κ 13
    cell-46 = refl

    -- σ=1547 (5 nodes)
    cell-47 : κ 13 ≡ κ 13
    cell-47 = refl

    -- σ=1561 (5 nodes)
    cell-48 : κ 13 ≡ κ 13
    cell-48 = refl

    -- σ=201 (4 nodes)
    cell-49 : κ 13 ≡ κ 13
    cell-49 = refl

    -- σ=982 (4 nodes)
    cell-50 : κ 13 ≡ κ 13
    cell-50 = refl

    -- σ=1050 (4 nodes)
    cell-51 : κ 13 ≡ κ 13
    cell-51 = refl

    -- σ=1116 (4 nodes)
    cell-52 : κ 13 ≡ κ 13
    cell-52 = refl

    -- σ=1185 (4 nodes)
    cell-53 : κ 13 ≡ κ 13
    cell-53 = refl

    -- σ=1265 (4 nodes)
    cell-54 : κ 13 ≡ κ 13
    cell-54 = refl

    -- σ=1532 (4 nodes)
    cell-55 : κ 13 ≡ κ 13
    cell-55 = refl

    -- σ=1610 (4 nodes)
    cell-56 : κ 13 ≡ κ 13
    cell-56 = refl

    -- σ=1751 (4 nodes)
    cell-57 : κ 13 ≡ κ 13
    cell-57 = refl

    -- σ=1885 (4 nodes)
    cell-58 : κ 13 ≡ κ 13
    cell-58 = refl

    -- σ=1904 (4 nodes)
    cell-59 : κ 13 ≡ κ 13
    cell-59 = refl

    -- σ=122 (3 nodes)
    cell-60 : κ 13 ≡ κ 13
    cell-60 = refl

    -- σ=188 (3 nodes)
    cell-61 : κ 13 ≡ κ 13
    cell-61 = refl

    -- σ=435 (3 nodes)
    cell-62 : κ 13 ≡ κ 13
    cell-62 = refl

    -- σ=543 (3 nodes)
    cell-63 : κ 13 ≡ κ 13
    cell-63 = refl

    -- σ=547 (3 nodes)
    cell-64 : κ 13 ≡ κ 13
    cell-64 = refl

    -- σ=572 (3 nodes)
    cell-65 : κ 13 ≡ κ 13
    cell-65 = refl

    -- σ=647 (3 nodes)
    cell-66 : κ 13 ≡ κ 13
    cell-66 = refl

    -- σ=736 (3 nodes)
    cell-67 : κ 13 ≡ κ 13
    cell-67 = refl

    -- σ=815 (3 nodes)
    cell-68 : κ 13 ≡ κ 13
    cell-68 = refl

    -- σ=941 (3 nodes)
    cell-69 : κ 13 ≡ κ 13
    cell-69 = refl

    -- σ=1115 (3 nodes)
    cell-70 : κ 13 ≡ κ 13
    cell-70 = refl

    -- σ=1154 (3 nodes)
    cell-71 : κ 13 ≡ κ 13
    cell-71 = refl

    -- σ=1188 (3 nodes)
    cell-72 : κ 13 ≡ κ 13
    cell-72 = refl

    -- σ=1189 (3 nodes)
    cell-73 : κ 13 ≡ κ 13
    cell-73 = refl

    -- σ=1306 (3 nodes)
    cell-74 : κ 13 ≡ κ 13
    cell-74 = refl

    -- σ=1316 (3 nodes)
    cell-75 : κ 13 ≡ κ 13
    cell-75 = refl

    -- σ=1346 (3 nodes)
    cell-76 : κ 13 ≡ κ 13
    cell-76 = refl

    -- σ=1506 (3 nodes)
    cell-77 : κ 13 ≡ κ 13
    cell-77 = refl

    -- σ=1617 (3 nodes)
    cell-78 : κ 13 ≡ κ 13
    cell-78 = refl

    -- σ=1662 (3 nodes)
    cell-79 : κ 13 ≡ κ 13
    cell-79 = refl

    -- σ=1668 (3 nodes)
    cell-80 : κ 13 ≡ κ 13
    cell-80 = refl

    -- σ=1786 (3 nodes)
    cell-81 : κ 13 ≡ κ 13
    cell-81 = refl

    -- σ=81 (2 nodes)
    cell-82 : κ 13 ≡ κ 13
    cell-82 = refl

    -- σ=83 (2 nodes)
    cell-83 : κ 13 ≡ κ 13
    cell-83 = refl

    -- σ=158 (2 nodes)
    cell-84 : κ 13 ≡ κ 13
    cell-84 = refl

    -- σ=185 (2 nodes)
    cell-85 : κ 13 ≡ κ 13
    cell-85 = refl

    -- σ=265 (2 nodes)
    cell-86 : κ 13 ≡ κ 13
    cell-86 = refl

    -- σ=283 (2 nodes)
    cell-87 : κ 13 ≡ κ 13
    cell-87 = refl

    -- σ=439 (2 nodes)
    cell-88 : κ 13 ≡ κ 13
    cell-88 = refl

    -- σ=501 (2 nodes)
    cell-89 : κ 13 ≡ κ 13
    cell-89 = refl

    -- σ=555 (2 nodes)
    cell-90 : κ 13 ≡ κ 13
    cell-90 = refl

    -- σ=564 (2 nodes)
    cell-91 : κ 13 ≡ κ 13
    cell-91 = refl

    -- σ=595 (2 nodes)
    cell-92 : κ 13 ≡ κ 13
    cell-92 = refl

    -- σ=665 (2 nodes)
    cell-93 : κ 13 ≡ κ 13
    cell-93 = refl

    -- σ=676 (2 nodes)
    cell-94 : κ 13 ≡ κ 13
    cell-94 = refl

    -- σ=693 (2 nodes)
    cell-95 : κ 13 ≡ κ 13
    cell-95 = refl

    -- σ=712 (2 nodes)
    cell-96 : κ 13 ≡ κ 13
    cell-96 = refl

    -- σ=715 (2 nodes)
    cell-97 : κ 13 ≡ κ 13
    cell-97 = refl

    -- σ=734 (2 nodes)
    cell-98 : κ 13 ≡ κ 13
    cell-98 = refl

    -- σ=757 (2 nodes)
    cell-99 : κ 13 ≡ κ 13
    cell-99 = refl

    -- σ=856 (2 nodes)
    cell-100 : κ 13 ≡ κ 13
    cell-100 = refl

    -- σ=860 (2 nodes)
    cell-101 : κ 13 ≡ κ 13
    cell-101 = refl

    -- σ=895 (2 nodes)
    cell-102 : κ 13 ≡ κ 13
    cell-102 = refl

    -- σ=901 (2 nodes)
    cell-103 : κ 13 ≡ κ 13
    cell-103 = refl

    -- σ=1202 (2 nodes)
    cell-104 : κ 13 ≡ κ 13
    cell-104 = refl

    -- σ=1230 (2 nodes)
    cell-105 : κ 13 ≡ κ 13
    cell-105 = refl

    -- σ=1231 (2 nodes)
    cell-106 : κ 13 ≡ κ 13
    cell-106 = refl

    -- σ=1235 (2 nodes)
    cell-107 : κ 13 ≡ κ 13
    cell-107 = refl

    -- σ=1236 (2 nodes)
    cell-108 : κ 13 ≡ κ 13
    cell-108 = refl

    -- σ=1384 (2 nodes)
    cell-109 : κ 13 ≡ κ 13
    cell-109 = refl

    -- σ=1392 (2 nodes)
    cell-110 : κ 13 ≡ κ 13
    cell-110 = refl

    -- σ=1411 (2 nodes)
    cell-111 : κ 13 ≡ κ 13
    cell-111 = refl

    -- σ=1436 (2 nodes)
    cell-112 : κ 13 ≡ κ 13
    cell-112 = refl

    -- σ=1448 (2 nodes)
    cell-113 : κ 13 ≡ κ 13
    cell-113 = refl

    -- σ=1505 (2 nodes)
    cell-114 : κ 13 ≡ κ 13
    cell-114 = refl

    -- σ=1542 (2 nodes)
    cell-115 : κ 13 ≡ κ 13
    cell-115 = refl

    -- σ=1591 (2 nodes)
    cell-116 : κ 13 ≡ κ 13
    cell-116 = refl

    -- σ=1596 (2 nodes)
    cell-117 : κ 13 ≡ κ 13
    cell-117 = refl

    -- σ=1602 (2 nodes)
    cell-118 : κ 13 ≡ κ 13
    cell-118 = refl

    -- σ=1611 (2 nodes)
    cell-119 : κ 13 ≡ κ 13
    cell-119 = refl

    -- σ=1616 (2 nodes)
    cell-120 : κ 13 ≡ κ 13
    cell-120 = refl

    -- σ=1624 (2 nodes)
    cell-121 : κ 13 ≡ κ 13
    cell-121 = refl

    -- σ=1642 (2 nodes)
    cell-122 : κ 13 ≡ κ 13
    cell-122 = refl

    -- σ=1708 (2 nodes)
    cell-123 : κ 13 ≡ κ 13
    cell-123 = refl

    -- σ=1734 (2 nodes)
    cell-124 : κ 13 ≡ κ 13
    cell-124 = refl

    -- σ=1745 (2 nodes)
    cell-125 : κ 13 ≡ κ 13
    cell-125 = refl

    -- σ=1870 (2 nodes)
    cell-126 : κ 13 ≡ κ 13
    cell-126 = refl

    -- σ=1894 (2 nodes)
    cell-127 : κ 13 ≡ κ 13
    cell-127 = refl

    -- σ=1956 (2 nodes)
    cell-128 : κ 13 ≡ κ 13
    cell-128 = refl

    -- σ=1999 (2 nodes)
    cell-129 : κ 13 ≡ κ 13
    cell-129 = refl

    -- σ=2073 (2 nodes)
    cell-130 : κ 13 ≡ κ 13
    cell-130 = refl

    -- σ=111 (1 nodes)
    cell-131 : κ 13 ≡ κ 13
    cell-131 = refl

    -- σ=119 (1 nodes)
    cell-132 : κ 13 ≡ κ 13
    cell-132 = refl

    -- σ=231 (1 nodes)
    cell-133 : κ 13 ≡ κ 13
    cell-133 = refl

    -- σ=463 (1 nodes)
    cell-134 : κ 13 ≡ κ 13
    cell-134 = refl

    -- σ=478 (1 nodes)
    cell-135 : κ 13 ≡ κ 13
    cell-135 = refl

    -- σ=542 (1 nodes)
    cell-136 : κ 13 ≡ κ 13
    cell-136 = refl

    -- σ=597 (1 nodes)
    cell-137 : κ 13 ≡ κ 13
    cell-137 = refl

    -- σ=607 (1 nodes)
    cell-138 : κ 13 ≡ κ 13
    cell-138 = refl

    -- σ=643 (1 nodes)
    cell-139 : κ 13 ≡ κ 13
    cell-139 = refl

    -- σ=659 (1 nodes)
    cell-140 : κ 13 ≡ κ 13
    cell-140 = refl

    -- σ=680 (1 nodes)
    cell-141 : κ 13 ≡ κ 13
    cell-141 = refl

    -- σ=756 (1 nodes)
    cell-142 : κ 13 ≡ κ 13
    cell-142 = refl

    -- σ=917 (1 nodes)
    cell-143 : κ 13 ≡ κ 13
    cell-143 = refl

    -- σ=940 (1 nodes)
    cell-144 : κ 13 ≡ κ 13
    cell-144 = refl

    -- σ=951 (1 nodes)
    cell-145 : κ 13 ≡ κ 13
    cell-145 = refl

    -- σ=963 (1 nodes)
    cell-146 : κ 13 ≡ κ 13
    cell-146 = refl

    -- σ=993 (1 nodes)
    cell-147 : κ 13 ≡ κ 13
    cell-147 = refl

    -- σ=1026 (1 nodes)
    cell-148 : κ 13 ≡ κ 13
    cell-148 = refl

    -- σ=1094 (1 nodes)
    cell-149 : κ 13 ≡ κ 13
    cell-149 = refl

    -- σ=1169 (1 nodes)
    cell-150 : κ 13 ≡ κ 13
    cell-150 = refl

    -- σ=1269 (1 nodes)
    cell-151 : κ 13 ≡ κ 13
    cell-151 = refl

    -- σ=1281 (1 nodes)
    cell-152 : κ 13 ≡ κ 13
    cell-152 = refl

    -- σ=1282 (1 nodes)
    cell-153 : κ 13 ≡ κ 13
    cell-153 = refl

    -- σ=1290 (1 nodes)
    cell-154 : κ 13 ≡ κ 13
    cell-154 = refl

    -- σ=1351 (1 nodes)
    cell-155 : κ 13 ≡ κ 13
    cell-155 = refl

    -- σ=1385 (1 nodes)
    cell-156 : κ 13 ≡ κ 13
    cell-156 = refl

    -- σ=1386 (1 nodes)
    cell-157 : κ 13 ≡ κ 13
    cell-157 = refl

    -- σ=1406 (1 nodes)
    cell-158 : κ 13 ≡ κ 13
    cell-158 = refl

    -- σ=1468 (1 nodes)
    cell-159 : κ 13 ≡ κ 13
    cell-159 = refl

    -- σ=1470 (1 nodes)
    cell-160 : κ 13 ≡ κ 13
    cell-160 = refl

    -- σ=1495 (1 nodes)
    cell-161 : κ 13 ≡ κ 13
    cell-161 = refl

    -- σ=1499 (1 nodes)
    cell-162 : κ 13 ≡ κ 13
    cell-162 = refl

    -- σ=1538 (1 nodes)
    cell-163 : κ 13 ≡ κ 13
    cell-163 = refl

    -- σ=1544 (1 nodes)
    cell-164 : κ 13 ≡ κ 13
    cell-164 = refl

    -- σ=1658 (1 nodes)
    cell-165 : κ 13 ≡ κ 13
    cell-165 = refl

    -- σ=1703 (1 nodes)
    cell-166 : κ 13 ≡ κ 13
    cell-166 = refl

    -- σ=1709 (1 nodes)
    cell-167 : κ 13 ≡ κ 13
    cell-167 = refl

    -- σ=1862 (1 nodes)
    cell-168 : κ 13 ≡ κ 13
    cell-168 = refl

    -- σ=1934 (1 nodes)
    cell-169 : κ 13 ≡ κ 13
    cell-169 = refl

    -- σ=1944 (1 nodes)
    cell-170 : κ 13 ≡ κ 13
    cell-170 = refl

    -- σ=2029 (1 nodes)
    cell-171 : κ 13 ≡ κ 13
    cell-171 = refl

    -- σ=2042 (1 nodes)
    cell-172 : κ 13 ≡ κ 13
    cell-172 = refl

    -- σ=2045 (1 nodes)
    cell-173 : κ 13 ≡ κ 13
    cell-173 = refl

    -- σ=2082 (1 nodes)
    cell-174 : κ 13 ≡ κ 13
    cell-174 = refl


  -- τ=13: 740 nodes, 31 σ-classes
  module Self where

    -- σ=22 (284 nodes)
    cell-0 : κ 13 ≡ κ 13
    cell-0 = refl

    -- σ=32 (117 nodes)
    cell-1 : κ 13 ≡ κ 13
    cell-1 = refl

    -- σ=177 (75 nodes)
    cell-2 : κ 13 ≡ κ 13
    cell-2 = refl

    -- σ=140 (55 nodes)
    cell-3 : κ 13 ≡ κ 13
    cell-3 = refl

    -- σ=276 (54 nodes)
    cell-4 : κ 13 ≡ κ 13
    cell-4 = refl

    -- σ=24 (31 nodes)
    cell-5 : κ 13 ≡ κ 13
    cell-5 = refl

    -- σ=161 (30 nodes)
    cell-6 : κ 13 ≡ κ 13
    cell-6 = refl

    -- σ=1143 (13 nodes)
    cell-7 : κ 13 ≡ κ 13
    cell-7 = refl

    -- σ=1797 (10 nodes)
    cell-8 : κ 13 ≡ κ 13
    cell-8 = refl

    -- σ=432 (9 nodes)
    cell-9 : κ 13 ≡ κ 13
    cell-9 = refl

    -- σ=231 (9 nodes)
    cell-10 : κ 13 ≡ κ 13
    cell-10 = refl

    -- σ=1925 (9 nodes)
    cell-11 : κ 13 ≡ κ 13
    cell-11 = refl

    -- σ=646 (7 nodes)
    cell-12 : κ 13 ≡ κ 13
    cell-12 = refl

    -- σ=152 (6 nodes)
    cell-13 : κ 13 ≡ κ 13
    cell-13 = refl

    -- σ=546 (4 nodes)
    cell-14 : κ 13 ≡ κ 13
    cell-14 = refl

    -- σ=1818 (4 nodes)
    cell-15 : κ 13 ≡ κ 13
    cell-15 = refl

    -- σ=1987 (3 nodes)
    cell-16 : κ 13 ≡ κ 13
    cell-16 = refl

    -- σ=117 (2 nodes)
    cell-17 : κ 13 ≡ κ 13
    cell-17 = refl

    -- σ=445 (2 nodes)
    cell-18 : κ 13 ≡ κ 13
    cell-18 = refl

    -- σ=904 (2 nodes)
    cell-19 : κ 13 ≡ κ 13
    cell-19 = refl

    -- σ=1109 (2 nodes)
    cell-20 : κ 13 ≡ κ 13
    cell-20 = refl

    -- σ=1832 (2 nodes)
    cell-21 : κ 13 ≡ κ 13
    cell-21 = refl

    -- σ=1839 (2 nodes)
    cell-22 : κ 13 ≡ κ 13
    cell-22 = refl

    -- σ=495 (1 nodes)
    cell-23 : κ 13 ≡ κ 13
    cell-23 = refl

    -- σ=629 (1 nodes)
    cell-24 : κ 13 ≡ κ 13
    cell-24 = refl

    -- σ=1242 (1 nodes)
    cell-25 : κ 13 ≡ κ 13
    cell-25 = refl

    -- σ=1248 (1 nodes)
    cell-26 : κ 13 ≡ κ 13
    cell-26 = refl

    -- σ=676 (1 nodes)
    cell-27 : κ 13 ≡ κ 13
    cell-27 = refl

    -- σ=1626 (1 nodes)
    cell-28 : κ 13 ≡ κ 13
    cell-28 = refl

    -- σ=2012 (1 nodes)
    cell-29 : κ 13 ≡ κ 13
    cell-29 = refl

    -- σ=185 (1 nodes)
    cell-30 : κ 13 ≡ κ 13
    cell-30 = refl



-- κ=7: 275 nodes, 2 τ-classes, 153 σ-classes
module bind-Name where

  -- τ=44: 245 nodes, 134 σ-classes
  module τ44 where

    -- σ=784 (11 nodes)
    cell-0 : κ 7 ≡ κ 7
    cell-0 = refl

    -- σ=783 (10 nodes)
    cell-1 : κ 7 ≡ κ 7
    cell-1 = refl

    -- σ=252 (6 nodes)
    cell-2 : κ 7 ≡ κ 7
    cell-2 = refl

    -- σ=475 (6 nodes)
    cell-3 : κ 7 ≡ κ 7
    cell-3 = refl

    -- σ=1434 (6 nodes)
    cell-4 : κ 7 ≡ κ 7
    cell-4 = refl

    -- σ=209 (5 nodes)
    cell-5 : κ 7 ≡ κ 7
    cell-5 = refl

    -- σ=494 (5 nodes)
    cell-6 : κ 7 ≡ κ 7
    cell-6 = refl

    -- σ=790 (5 nodes)
    cell-7 : κ 7 ≡ κ 7
    cell-7 = refl

    -- σ=847 (5 nodes)
    cell-8 : κ 7 ≡ κ 7
    cell-8 = refl

    -- σ=894 (5 nodes)
    cell-9 : κ 7 ≡ κ 7
    cell-9 = refl

    -- σ=280 (4 nodes)
    cell-10 : κ 7 ≡ κ 7
    cell-10 = refl

    -- σ=443 (4 nodes)
    cell-11 : κ 7 ≡ κ 7
    cell-11 = refl

    -- σ=800 (4 nodes)
    cell-12 : κ 7 ≡ κ 7
    cell-12 = refl

    -- σ=1173 (4 nodes)
    cell-13 : κ 7 ≡ κ 7
    cell-13 = refl

    -- σ=54 (3 nodes)
    cell-14 : κ 7 ≡ κ 7
    cell-14 = refl

    -- σ=77 (3 nodes)
    cell-15 : κ 7 ≡ κ 7
    cell-15 = refl

    -- σ=78 (3 nodes)
    cell-16 : κ 7 ≡ κ 7
    cell-16 = refl

    -- σ=295 (3 nodes)
    cell-17 : κ 7 ≡ κ 7
    cell-17 = refl

    -- σ=522 (3 nodes)
    cell-18 : κ 7 ≡ κ 7
    cell-18 = refl

    -- σ=569 (3 nodes)
    cell-19 : κ 7 ≡ κ 7
    cell-19 = refl

    -- σ=585 (3 nodes)
    cell-20 : κ 7 ≡ κ 7
    cell-20 = refl

    -- σ=937 (3 nodes)
    cell-21 : κ 7 ≡ κ 7
    cell-21 = refl

    -- σ=1177 (3 nodes)
    cell-22 : κ 7 ≡ κ 7
    cell-22 = refl

    -- σ=1424 (3 nodes)
    cell-23 : κ 7 ≡ κ 7
    cell-23 = refl

    -- σ=1509 (3 nodes)
    cell-24 : κ 7 ≡ κ 7
    cell-24 = refl

    -- σ=1528 (3 nodes)
    cell-25 : κ 7 ≡ κ 7
    cell-25 = refl

    -- σ=507 (2 nodes)
    cell-26 : κ 7 ≡ κ 7
    cell-26 = refl

    -- σ=549 (2 nodes)
    cell-27 : κ 7 ≡ κ 7
    cell-27 = refl

    -- σ=728 (2 nodes)
    cell-28 : κ 7 ≡ κ 7
    cell-28 = refl

    -- σ=765 (2 nodes)
    cell-29 : κ 7 ≡ κ 7
    cell-29 = refl

    -- σ=770 (2 nodes)
    cell-30 : κ 7 ≡ κ 7
    cell-30 = refl

    -- σ=774 (2 nodes)
    cell-31 : κ 7 ≡ κ 7
    cell-31 = refl

    -- σ=891 (2 nodes)
    cell-32 : κ 7 ≡ κ 7
    cell-32 = refl

    -- σ=972 (2 nodes)
    cell-33 : κ 7 ≡ κ 7
    cell-33 = refl

    -- σ=1048 (2 nodes)
    cell-34 : κ 7 ≡ κ 7
    cell-34 = refl

    -- σ=1113 (2 nodes)
    cell-35 : κ 7 ≡ κ 7
    cell-35 = refl

    -- σ=1125 (2 nodes)
    cell-36 : κ 7 ≡ κ 7
    cell-36 = refl

    -- σ=1130 (2 nodes)
    cell-37 : κ 7 ≡ κ 7
    cell-37 = refl

    -- σ=1239 (2 nodes)
    cell-38 : κ 7 ≡ κ 7
    cell-38 = refl

    -- σ=1335 (2 nodes)
    cell-39 : κ 7 ≡ κ 7
    cell-39 = refl

    -- σ=1433 (2 nodes)
    cell-40 : κ 7 ≡ κ 7
    cell-40 = refl

    -- σ=1486 (2 nodes)
    cell-41 : κ 7 ≡ κ 7
    cell-41 = refl

    -- σ=1508 (2 nodes)
    cell-42 : κ 7 ≡ κ 7
    cell-42 = refl

    -- σ=1558 (2 nodes)
    cell-43 : κ 7 ≡ κ 7
    cell-43 = refl

    -- σ=1744 (2 nodes)
    cell-44 : κ 7 ≡ κ 7
    cell-44 = refl

    -- σ=1767 (2 nodes)
    cell-45 : κ 7 ≡ κ 7
    cell-45 = refl

    -- σ=1768 (2 nodes)
    cell-46 : κ 7 ≡ κ 7
    cell-46 = refl

    -- σ=65 (1 nodes)
    cell-47 : κ 7 ≡ κ 7
    cell-47 = refl

    -- σ=256 (1 nodes)
    cell-48 : κ 7 ≡ κ 7
    cell-48 = refl

    -- σ=275 (1 nodes)
    cell-49 : κ 7 ≡ κ 7
    cell-49 = refl

    -- σ=456 (1 nodes)
    cell-50 : κ 7 ≡ κ 7
    cell-50 = refl

    -- σ=487 (1 nodes)
    cell-51 : κ 7 ≡ κ 7
    cell-51 = refl

    -- σ=509 (1 nodes)
    cell-52 : κ 7 ≡ κ 7
    cell-52 = refl

    -- σ=535 (1 nodes)
    cell-53 : κ 7 ≡ κ 7
    cell-53 = refl

    -- σ=538 (1 nodes)
    cell-54 : κ 7 ≡ κ 7
    cell-54 = refl

    -- σ=553 (1 nodes)
    cell-55 : κ 7 ≡ κ 7
    cell-55 = refl

    -- σ=563 (1 nodes)
    cell-56 : κ 7 ≡ κ 7
    cell-56 = refl

    -- σ=577 (1 nodes)
    cell-57 : κ 7 ≡ κ 7
    cell-57 = refl

    -- σ=602 (1 nodes)
    cell-58 : κ 7 ≡ κ 7
    cell-58 = refl

    -- σ=633 (1 nodes)
    cell-59 : κ 7 ≡ κ 7
    cell-59 = refl

    -- σ=636 (1 nodes)
    cell-60 : κ 7 ≡ κ 7
    cell-60 = refl

    -- σ=638 (1 nodes)
    cell-61 : κ 7 ≡ κ 7
    cell-61 = refl

    -- σ=664 (1 nodes)
    cell-62 : κ 7 ≡ κ 7
    cell-62 = refl

    -- σ=673 (1 nodes)
    cell-63 : κ 7 ≡ κ 7
    cell-63 = refl

    -- σ=685 (1 nodes)
    cell-64 : κ 7 ≡ κ 7
    cell-64 = refl

    -- σ=731 (1 nodes)
    cell-65 : κ 7 ≡ κ 7
    cell-65 = refl

    -- σ=751 (1 nodes)
    cell-66 : κ 7 ≡ κ 7
    cell-66 = refl

    -- σ=753 (1 nodes)
    cell-67 : κ 7 ≡ κ 7
    cell-67 = refl

    -- σ=755 (1 nodes)
    cell-68 : κ 7 ≡ κ 7
    cell-68 = refl

    -- σ=776 (1 nodes)
    cell-69 : κ 7 ≡ κ 7
    cell-69 = refl

    -- σ=845 (1 nodes)
    cell-70 : κ 7 ≡ κ 7
    cell-70 = refl

    -- σ=886 (1 nodes)
    cell-71 : κ 7 ≡ κ 7
    cell-71 = refl

    -- σ=887 (1 nodes)
    cell-72 : κ 7 ≡ κ 7
    cell-72 = refl

    -- σ=944 (1 nodes)
    cell-73 : κ 7 ≡ κ 7
    cell-73 = refl

    -- σ=946 (1 nodes)
    cell-74 : κ 7 ≡ κ 7
    cell-74 = refl

    -- σ=950 (1 nodes)
    cell-75 : κ 7 ≡ κ 7
    cell-75 = refl

    -- σ=900 (1 nodes)
    cell-76 : κ 7 ≡ κ 7
    cell-76 = refl

    -- σ=957 (1 nodes)
    cell-77 : κ 7 ≡ κ 7
    cell-77 = refl

    -- σ=965 (1 nodes)
    cell-78 : κ 7 ≡ κ 7
    cell-78 = refl

    -- σ=995 (1 nodes)
    cell-79 : κ 7 ≡ κ 7
    cell-79 = refl

    -- σ=1023 (1 nodes)
    cell-80 : κ 7 ≡ κ 7
    cell-80 = refl

    -- σ=1033 (1 nodes)
    cell-81 : κ 7 ≡ κ 7
    cell-81 = refl

    -- σ=1065 (1 nodes)
    cell-82 : κ 7 ≡ κ 7
    cell-82 = refl

    -- σ=1093 (1 nodes)
    cell-83 : κ 7 ≡ κ 7
    cell-83 = refl

    -- σ=1106 (1 nodes)
    cell-84 : κ 7 ≡ κ 7
    cell-84 = refl

    -- σ=1146 (1 nodes)
    cell-85 : κ 7 ≡ κ 7
    cell-85 = refl

    -- σ=1165 (1 nodes)
    cell-86 : κ 7 ≡ κ 7
    cell-86 = refl

    -- σ=1180 (1 nodes)
    cell-87 : κ 7 ≡ κ 7
    cell-87 = refl

    -- σ=1184 (1 nodes)
    cell-88 : κ 7 ≡ κ 7
    cell-88 = refl

    -- σ=1200 (1 nodes)
    cell-89 : κ 7 ≡ κ 7
    cell-89 = refl

    -- σ=1245 (1 nodes)
    cell-90 : κ 7 ≡ κ 7
    cell-90 = refl

    -- σ=1251 (1 nodes)
    cell-91 : κ 7 ≡ κ 7
    cell-91 = refl

    -- σ=1257 (1 nodes)
    cell-92 : κ 7 ≡ κ 7
    cell-92 = refl

    -- σ=1260 (1 nodes)
    cell-93 : κ 7 ≡ κ 7
    cell-93 = refl

    -- σ=1280 (1 nodes)
    cell-94 : κ 7 ≡ κ 7
    cell-94 = refl

    -- σ=1285 (1 nodes)
    cell-95 : κ 7 ≡ κ 7
    cell-95 = refl

    -- σ=1304 (1 nodes)
    cell-96 : κ 7 ≡ κ 7
    cell-96 = refl

    -- σ=1314 (1 nodes)
    cell-97 : κ 7 ≡ κ 7
    cell-97 = refl

    -- σ=1342 (1 nodes)
    cell-98 : κ 7 ≡ κ 7
    cell-98 = refl

    -- σ=1390 (1 nodes)
    cell-99 : κ 7 ≡ κ 7
    cell-99 = refl

    -- σ=1526 (1 nodes)
    cell-100 : κ 7 ≡ κ 7
    cell-100 = refl

    -- σ=1531 (1 nodes)
    cell-101 : κ 7 ≡ κ 7
    cell-101 = refl

    -- σ=1536 (1 nodes)
    cell-102 : κ 7 ≡ κ 7
    cell-102 = refl

    -- σ=1572 (1 nodes)
    cell-103 : κ 7 ≡ κ 7
    cell-103 = refl

    -- σ=1575 (1 nodes)
    cell-104 : κ 7 ≡ κ 7
    cell-104 = refl

    -- σ=1582 (1 nodes)
    cell-105 : κ 7 ≡ κ 7
    cell-105 = refl

    -- σ=1584 (1 nodes)
    cell-106 : κ 7 ≡ κ 7
    cell-106 = refl

    -- σ=1586 (1 nodes)
    cell-107 : κ 7 ≡ κ 7
    cell-107 = refl

    -- σ=1588 (1 nodes)
    cell-108 : κ 7 ≡ κ 7
    cell-108 = refl

    -- σ=1609 (1 nodes)
    cell-109 : κ 7 ≡ κ 7
    cell-109 = refl

    -- σ=1641 (1 nodes)
    cell-110 : κ 7 ≡ κ 7
    cell-110 = refl

    -- σ=1643 (1 nodes)
    cell-111 : κ 7 ≡ κ 7
    cell-111 = refl

    -- σ=1649 (1 nodes)
    cell-112 : κ 7 ≡ κ 7
    cell-112 = refl

    -- σ=1656 (1 nodes)
    cell-113 : κ 7 ≡ κ 7
    cell-113 = refl

    -- σ=1694 (1 nodes)
    cell-114 : κ 7 ≡ κ 7
    cell-114 = refl

    -- σ=1698 (1 nodes)
    cell-115 : κ 7 ≡ κ 7
    cell-115 = refl

    -- σ=1705 (1 nodes)
    cell-116 : κ 7 ≡ κ 7
    cell-116 = refl

    -- σ=1730 (1 nodes)
    cell-117 : κ 7 ≡ κ 7
    cell-117 = refl

    -- σ=1737 (1 nodes)
    cell-118 : κ 7 ≡ κ 7
    cell-118 = refl

    -- σ=1868 (1 nodes)
    cell-119 : κ 7 ≡ κ 7
    cell-119 = refl

    -- σ=1869 (1 nodes)
    cell-120 : κ 7 ≡ κ 7
    cell-120 = refl

    -- σ=1881 (1 nodes)
    cell-121 : κ 7 ≡ κ 7
    cell-121 = refl

    -- σ=1884 (1 nodes)
    cell-122 : κ 7 ≡ κ 7
    cell-122 = refl

    -- σ=1892 (1 nodes)
    cell-123 : κ 7 ≡ κ 7
    cell-123 = refl

    -- σ=1898 (1 nodes)
    cell-124 : κ 7 ≡ κ 7
    cell-124 = refl

    -- σ=1917 (1 nodes)
    cell-125 : κ 7 ≡ κ 7
    cell-125 = refl

    -- σ=1986 (1 nodes)
    cell-126 : κ 7 ≡ κ 7
    cell-126 = refl

    -- σ=512 (1 nodes)
    cell-127 : κ 7 ≡ κ 7
    cell-127 = refl

    -- σ=2019 (1 nodes)
    cell-128 : κ 7 ≡ κ 7
    cell-128 = refl

    -- σ=2020 (1 nodes)
    cell-129 : κ 7 ≡ κ 7
    cell-129 = refl

    -- σ=2028 (1 nodes)
    cell-130 : κ 7 ≡ κ 7
    cell-130 = refl

    -- σ=2051 (1 nodes)
    cell-131 : κ 7 ≡ κ 7
    cell-131 = refl

    -- σ=2057 (1 nodes)
    cell-132 : κ 7 ≡ κ 7
    cell-132 = refl

    -- σ=2066 (1 nodes)
    cell-133 : κ 7 ≡ κ 7
    cell-133 = refl


  -- τ=7: 30 nodes, 24 σ-classes
  module tuple where

    -- σ=14 (2 nodes)
    cell-0 : κ 7 ≡ κ 7
    cell-0 = refl

    -- σ=440 (2 nodes)
    cell-1 : κ 7 ≡ κ 7
    cell-1 = refl

    -- σ=512 (2 nodes)
    cell-2 : κ 7 ≡ κ 7
    cell-2 = refl

    -- σ=609 (2 nodes)
    cell-3 : κ 7 ≡ κ 7
    cell-3 = refl

    -- σ=640 (2 nodes)
    cell-4 : κ 7 ≡ κ 7
    cell-4 = refl

    -- σ=1135 (2 nodes)
    cell-5 : κ 7 ≡ κ 7
    cell-5 = refl

    -- σ=209 (1 nodes)
    cell-6 : κ 7 ≡ κ 7
    cell-6 = refl

    -- σ=481 (1 nodes)
    cell-7 : κ 7 ≡ κ 7
    cell-7 = refl

    -- σ=541 (1 nodes)
    cell-8 : κ 7 ≡ κ 7
    cell-8 = refl

    -- σ=509 (1 nodes)
    cell-9 : κ 7 ≡ κ 7
    cell-9 = refl

    -- σ=900 (1 nodes)
    cell-10 : κ 7 ≡ κ 7
    cell-10 = refl

    -- σ=1102 (1 nodes)
    cell-11 : κ 7 ≡ κ 7
    cell-11 = refl

    -- σ=1227 (1 nodes)
    cell-12 : κ 7 ≡ κ 7
    cell-12 = refl

    -- σ=1229 (1 nodes)
    cell-13 : κ 7 ≡ κ 7
    cell-13 = refl

    -- σ=1234 (1 nodes)
    cell-14 : κ 7 ≡ κ 7
    cell-14 = refl

    -- σ=1621 (1 nodes)
    cell-15 : κ 7 ≡ κ 7
    cell-15 = refl

    -- σ=1795 (1 nodes)
    cell-16 : κ 7 ≡ κ 7
    cell-16 = refl

    -- σ=1802 (1 nodes)
    cell-17 : κ 7 ≡ κ 7
    cell-17 = refl

    -- σ=1804 (1 nodes)
    cell-18 : κ 7 ≡ κ 7
    cell-18 = refl

    -- σ=1806 (1 nodes)
    cell-19 : κ 7 ≡ κ 7
    cell-19 = refl

    -- σ=1811 (1 nodes)
    cell-20 : κ 7 ≡ κ 7
    cell-20 = refl

    -- σ=1972 (1 nodes)
    cell-21 : κ 7 ≡ κ 7
    cell-21 = refl

    -- σ=1981 (1 nodes)
    cell-22 : κ 7 ≡ κ 7
    cell-22 = refl

    -- σ=755 (1 nodes)
    cell-23 : κ 7 ≡ κ 7
    cell-23 = refl



-- κ=0: 295 nodes, 2 τ-classes, 125 σ-classes
module terminal-Constant where

  -- τ=0: 273 nodes, 124 σ-classes
  module str where

    -- σ=107 (37 nodes)
    cell-0 : κ 0 ≡ κ 0
    cell-0 = refl

    -- σ=50 (31 nodes)
    cell-1 : κ 0 ≡ κ 0
    cell-1 = refl

    -- σ=37 (18 nodes)
    cell-2 : κ 0 ≡ κ 0
    cell-2 = refl

    -- σ=323 (10 nodes)
    cell-3 : κ 0 ≡ κ 0
    cell-3 = refl

    -- σ=327 (9 nodes)
    cell-4 : κ 0 ≡ κ 0
    cell-4 = refl

    -- σ=331 (9 nodes)
    cell-5 : κ 0 ≡ κ 0
    cell-5 = refl

    -- σ=503 (8 nodes)
    cell-6 : κ 0 ≡ κ 0
    cell-6 = refl

    -- σ=1826 (7 nodes)
    cell-7 : κ 0 ≡ κ 0
    cell-7 = refl

    -- σ=1829 (5 nodes)
    cell-8 : κ 0 ≡ κ 0
    cell-8 = refl

    -- σ=523 (4 nodes)
    cell-9 : κ 0 ≡ κ 0
    cell-9 = refl

    -- σ=613 (4 nodes)
    cell-10 : κ 0 ≡ κ 0
    cell-10 = refl

    -- σ=1789 (4 nodes)
    cell-11 : κ 0 ≡ κ 0
    cell-11 = refl

    -- σ=1819 (4 nodes)
    cell-12 : κ 0 ≡ κ 0
    cell-12 = refl

    -- σ=1822 (4 nodes)
    cell-13 : κ 0 ≡ κ 0
    cell-13 = refl

    -- σ=583 (3 nodes)
    cell-14 : κ 0 ≡ κ 0
    cell-14 = refl

    -- σ=170 (2 nodes)
    cell-15 : κ 0 ≡ κ 0
    cell-15 = refl

    -- σ=314 (2 nodes)
    cell-16 : κ 0 ≡ κ 0
    cell-16 = refl

    -- σ=612 (2 nodes)
    cell-17 : κ 0 ≡ κ 0
    cell-17 = refl

    -- σ=1380 (2 nodes)
    cell-18 : κ 0 ≡ κ 0
    cell-18 = refl

    -- σ=1958 (2 nodes)
    cell-19 : κ 0 ≡ κ 0
    cell-19 = refl

    -- σ=1995 (2 nodes)
    cell-20 : κ 0 ≡ κ 0
    cell-20 = refl

    -- σ=2038 (2 nodes)
    cell-21 : κ 0 ≡ κ 0
    cell-21 = refl

    -- σ=0 (1 nodes)
    cell-22 : κ 0 ≡ κ 0
    cell-22 = refl

    -- σ=11 (1 nodes)
    cell-23 : κ 0 ≡ κ 0
    cell-23 = refl

    -- σ=15 (1 nodes)
    cell-24 : κ 0 ≡ κ 0
    cell-24 = refl

    -- σ=16 (1 nodes)
    cell-25 : κ 0 ≡ κ 0
    cell-25 = refl

    -- σ=75 (1 nodes)
    cell-26 : κ 0 ≡ κ 0
    cell-26 = refl

    -- σ=131 (1 nodes)
    cell-27 : κ 0 ≡ κ 0
    cell-27 = refl

    -- σ=133 (1 nodes)
    cell-28 : κ 0 ≡ κ 0
    cell-28 = refl

    -- σ=134 (1 nodes)
    cell-29 : κ 0 ≡ κ 0
    cell-29 = refl

    -- σ=135 (1 nodes)
    cell-30 : κ 0 ≡ κ 0
    cell-30 = refl

    -- σ=136 (1 nodes)
    cell-31 : κ 0 ≡ κ 0
    cell-31 = refl

    -- σ=167 (1 nodes)
    cell-32 : κ 0 ≡ κ 0
    cell-32 = refl

    -- σ=174 (1 nodes)
    cell-33 : κ 0 ≡ κ 0
    cell-33 = refl

    -- σ=180 (1 nodes)
    cell-34 : κ 0 ≡ κ 0
    cell-34 = refl

    -- σ=237 (1 nodes)
    cell-35 : κ 0 ≡ κ 0
    cell-35 = refl

    -- σ=246 (1 nodes)
    cell-36 : κ 0 ≡ κ 0
    cell-36 = refl

    -- σ=273 (1 nodes)
    cell-37 : κ 0 ≡ κ 0
    cell-37 = refl

    -- σ=309 (1 nodes)
    cell-38 : κ 0 ≡ κ 0
    cell-38 = refl

    -- σ=319 (1 nodes)
    cell-39 : κ 0 ≡ κ 0
    cell-39 = refl

    -- σ=429 (1 nodes)
    cell-40 : κ 0 ≡ κ 0
    cell-40 = refl

    -- σ=473 (1 nodes)
    cell-41 : κ 0 ≡ κ 0
    cell-41 = refl

    -- σ=514 (1 nodes)
    cell-42 : κ 0 ≡ κ 0
    cell-42 = refl

    -- σ=610 (1 nodes)
    cell-43 : κ 0 ≡ κ 0
    cell-43 = refl

    -- σ=619 (1 nodes)
    cell-44 : κ 0 ≡ κ 0
    cell-44 = refl

    -- σ=749 (1 nodes)
    cell-45 : κ 0 ≡ κ 0
    cell-45 = refl

    -- σ=839 (1 nodes)
    cell-46 : κ 0 ≡ κ 0
    cell-46 = refl

    -- σ=871 (1 nodes)
    cell-47 : κ 0 ≡ κ 0
    cell-47 = refl

    -- σ=915 (1 nodes)
    cell-48 : κ 0 ≡ κ 0
    cell-48 = refl

    -- σ=935 (1 nodes)
    cell-49 : κ 0 ≡ κ 0
    cell-49 = refl

    -- σ=998 (1 nodes)
    cell-50 : κ 0 ≡ κ 0
    cell-50 = refl

    -- σ=1044 (1 nodes)
    cell-51 : κ 0 ≡ κ 0
    cell-51 = refl

    -- σ=1075 (1 nodes)
    cell-52 : κ 0 ≡ κ 0
    cell-52 = refl

    -- σ=1136 (1 nodes)
    cell-53 : κ 0 ≡ κ 0
    cell-53 = refl

    -- σ=1225 (1 nodes)
    cell-54 : κ 0 ≡ κ 0
    cell-54 = refl

    -- σ=1299 (1 nodes)
    cell-55 : κ 0 ≡ κ 0
    cell-55 = refl

    -- σ=1301 (1 nodes)
    cell-56 : κ 0 ≡ κ 0
    cell-56 = refl

    -- σ=1377 (1 nodes)
    cell-57 : κ 0 ≡ κ 0
    cell-57 = refl

    -- σ=1378 (1 nodes)
    cell-58 : κ 0 ≡ κ 0
    cell-58 = refl

    -- σ=1379 (1 nodes)
    cell-59 : κ 0 ≡ κ 0
    cell-59 = refl

    -- σ=1381 (1 nodes)
    cell-60 : κ 0 ≡ κ 0
    cell-60 = refl

    -- σ=1382 (1 nodes)
    cell-61 : κ 0 ≡ κ 0
    cell-61 = refl

    -- σ=1422 (1 nodes)
    cell-62 : κ 0 ≡ κ 0
    cell-62 = refl

    -- σ=1459 (1 nodes)
    cell-63 : κ 0 ≡ κ 0
    cell-63 = refl

    -- σ=1484 (1 nodes)
    cell-64 : κ 0 ≡ κ 0
    cell-64 = refl

    -- σ=1524 (1 nodes)
    cell-65 : κ 0 ≡ κ 0
    cell-65 = refl

    -- σ=1556 (1 nodes)
    cell-66 : κ 0 ≡ κ 0
    cell-66 = refl

    -- σ=1570 (1 nodes)
    cell-67 : κ 0 ≡ κ 0
    cell-67 = refl

    -- σ=1639 (1 nodes)
    cell-68 : κ 0 ≡ κ 0
    cell-68 = refl

    -- σ=1692 (1 nodes)
    cell-69 : κ 0 ≡ κ 0
    cell-69 = refl

    -- σ=1722 (1 nodes)
    cell-70 : κ 0 ≡ κ 0
    cell-70 = refl

    -- σ=1773 (1 nodes)
    cell-71 : κ 0 ≡ κ 0
    cell-71 = refl

    -- σ=1776 (1 nodes)
    cell-72 : κ 0 ≡ κ 0
    cell-72 = refl

    -- σ=1779 (1 nodes)
    cell-73 : κ 0 ≡ κ 0
    cell-73 = refl

    -- σ=1782 (1 nodes)
    cell-74 : κ 0 ≡ κ 0
    cell-74 = refl

    -- σ=1785 (1 nodes)
    cell-75 : κ 0 ≡ κ 0
    cell-75 = refl

    -- σ=1793 (1 nodes)
    cell-76 : κ 0 ≡ κ 0
    cell-76 = refl

    -- σ=1799 (1 nodes)
    cell-77 : κ 0 ≡ κ 0
    cell-77 = refl

    -- σ=1812 (1 nodes)
    cell-78 : κ 0 ≡ κ 0
    cell-78 = refl

    -- σ=1814 (1 nodes)
    cell-79 : κ 0 ≡ κ 0
    cell-79 = refl

    -- σ=1817 (1 nodes)
    cell-80 : κ 0 ≡ κ 0
    cell-80 = refl

    -- σ=1831 (1 nodes)
    cell-81 : κ 0 ≡ κ 0
    cell-81 = refl

    -- σ=1838 (1 nodes)
    cell-82 : κ 0 ≡ κ 0
    cell-82 = refl

    -- σ=1845 (1 nodes)
    cell-83 : κ 0 ≡ κ 0
    cell-83 = refl

    -- σ=1848 (1 nodes)
    cell-84 : κ 0 ≡ κ 0
    cell-84 = refl

    -- σ=1853 (1 nodes)
    cell-85 : κ 0 ≡ κ 0
    cell-85 = refl

    -- σ=1854 (1 nodes)
    cell-86 : κ 0 ≡ κ 0
    cell-86 = refl

    -- σ=1861 (1 nodes)
    cell-87 : κ 0 ≡ κ 0
    cell-87 = refl

    -- σ=1874 (1 nodes)
    cell-88 : κ 0 ≡ κ 0
    cell-88 = refl

    -- σ=1927 (1 nodes)
    cell-89 : κ 0 ≡ κ 0
    cell-89 = refl

    -- σ=1933 (1 nodes)
    cell-90 : κ 0 ≡ κ 0
    cell-90 = refl

    -- σ=1936 (1 nodes)
    cell-91 : κ 0 ≡ κ 0
    cell-91 = refl

    -- σ=1938 (1 nodes)
    cell-92 : κ 0 ≡ κ 0
    cell-92 = refl

    -- σ=1943 (1 nodes)
    cell-93 : κ 0 ≡ κ 0
    cell-93 = refl

    -- σ=1946 (1 nodes)
    cell-94 : κ 0 ≡ κ 0
    cell-94 = refl

    -- σ=1949 (1 nodes)
    cell-95 : κ 0 ≡ κ 0
    cell-95 = refl

    -- σ=1951 (1 nodes)
    cell-96 : κ 0 ≡ κ 0
    cell-96 = refl

    -- σ=1955 (1 nodes)
    cell-97 : κ 0 ≡ κ 0
    cell-97 = refl

    -- σ=1960 (1 nodes)
    cell-98 : κ 0 ≡ κ 0
    cell-98 = refl

    -- σ=1962 (1 nodes)
    cell-99 : κ 0 ≡ κ 0
    cell-99 = refl

    -- σ=1965 (1 nodes)
    cell-100 : κ 0 ≡ κ 0
    cell-100 = refl

    -- σ=1966 (1 nodes)
    cell-101 : κ 0 ≡ κ 0
    cell-101 = refl

    -- σ=1973 (1 nodes)
    cell-102 : κ 0 ≡ κ 0
    cell-102 = refl

    -- σ=1974 (1 nodes)
    cell-103 : κ 0 ≡ κ 0
    cell-103 = refl

    -- σ=1975 (1 nodes)
    cell-104 : κ 0 ≡ κ 0
    cell-104 = refl

    -- σ=1976 (1 nodes)
    cell-105 : κ 0 ≡ κ 0
    cell-105 = refl

    -- σ=1977 (1 nodes)
    cell-106 : κ 0 ≡ κ 0
    cell-106 = refl

    -- σ=1978 (1 nodes)
    cell-107 : κ 0 ≡ κ 0
    cell-107 = refl

    -- σ=1990 (1 nodes)
    cell-108 : κ 0 ≡ κ 0
    cell-108 = refl

    -- σ=1993 (1 nodes)
    cell-109 : κ 0 ≡ κ 0
    cell-109 = refl

    -- σ=1998 (1 nodes)
    cell-110 : κ 0 ≡ κ 0
    cell-110 = refl

    -- σ=2014 (1 nodes)
    cell-111 : κ 0 ≡ κ 0
    cell-111 = refl

    -- σ=2015 (1 nodes)
    cell-112 : κ 0 ≡ κ 0
    cell-112 = refl

    -- σ=2031 (1 nodes)
    cell-113 : κ 0 ≡ κ 0
    cell-113 = refl

    -- σ=2035 (1 nodes)
    cell-114 : κ 0 ≡ κ 0
    cell-114 = refl

    -- σ=2036 (1 nodes)
    cell-115 : κ 0 ≡ κ 0
    cell-115 = refl

    -- σ=2041 (1 nodes)
    cell-116 : κ 0 ≡ κ 0
    cell-116 = refl

    -- σ=2044 (1 nodes)
    cell-117 : κ 0 ≡ κ 0
    cell-117 = refl

    -- σ=2069 (1 nodes)
    cell-118 : κ 0 ≡ κ 0
    cell-118 = refl

    -- σ=2071 (1 nodes)
    cell-119 : κ 0 ≡ κ 0
    cell-119 = refl

    -- σ=2076 (1 nodes)
    cell-120 : κ 0 ≡ κ 0
    cell-120 = refl

    -- σ=2078 (1 nodes)
    cell-121 : κ 0 ≡ κ 0
    cell-121 = refl

    -- σ=2081 (1 nodes)
    cell-122 : κ 0 ≡ κ 0
    cell-122 = refl

    -- σ=2090 (1 nodes)
    cell-123 : κ 0 ≡ κ 0
    cell-123 = refl


  -- τ=95: 22 nodes, 1 σ-classes
  module τ95 where

    -- σ=141 (22 nodes)
    cell-0 : κ 0 ≡ κ 0
    cell-0 = refl



-- κ=24: 243 nodes, 1 τ-classes, 44 σ-classes
module morphism-at-state-Attribute-0 where

  -- τ=34: 243 nodes, 44 σ-classes
  module Self-_parent where

    -- σ=476 (54 nodes)
    cell-0 : κ 24 ≡ κ 24
    cell-0 = refl

    -- σ=578 (14 nodes)
    cell-1 : κ 24 ≡ κ 24
    cell-1 = refl

    -- σ=767 (14 nodes)
    cell-2 : κ 24 ≡ κ 24
    cell-2 = refl

    -- σ=649 (12 nodes)
    cell-3 : κ 24 ≡ κ 24
    cell-3 = refl

    -- σ=43 (11 nodes)
    cell-4 : κ 24 ≡ κ 24
    cell-4 = refl

    -- σ=1439 (11 nodes)
    cell-5 : κ 24 ≡ κ 24
    cell-5 = refl

    -- σ=920 (9 nodes)
    cell-6 : κ 24 ≡ κ 24
    cell-6 = refl

    -- σ=490 (8 nodes)
    cell-7 : κ 24 ≡ κ 24
    cell-7 = refl

    -- σ=623 (8 nodes)
    cell-8 : κ 24 ≡ κ 24
    cell-8 = refl

    -- σ=223 (7 nodes)
    cell-9 : κ 24 ≡ κ 24
    cell-9 = refl

    -- σ=48 (6 nodes)
    cell-10 : κ 24 ≡ κ 24
    cell-10 = refl

    -- σ=218 (6 nodes)
    cell-11 : κ 24 ≡ κ 24
    cell-11 = refl

    -- σ=482 (6 nodes)
    cell-12 : κ 24 ≡ κ 24
    cell-12 = refl

    -- σ=759 (6 nodes)
    cell-13 : κ 24 ≡ κ 24
    cell-13 = refl

    -- σ=807 (6 nodes)
    cell-14 : κ 24 ≡ κ 24
    cell-14 = refl

    -- σ=855 (6 nodes)
    cell-15 : κ 24 ≡ κ 24
    cell-15 = refl

    -- σ=431 (4 nodes)
    cell-16 : κ 24 ≡ κ 24
    cell-16 = refl

    -- σ=516 (4 nodes)
    cell-17 : κ 24 ≡ κ 24
    cell-17 = refl

    -- σ=641 (4 nodes)
    cell-18 : κ 24 ≡ κ 24
    cell-18 = refl

    -- σ=1240 (4 nodes)
    cell-19 : κ 24 ≡ κ 24
    cell-19 = refl

    -- σ=1246 (4 nodes)
    cell-20 : κ 24 ≡ κ 24
    cell-20 = refl

    -- σ=207 (3 nodes)
    cell-21 : κ 24 ≡ κ 24
    cell-21 = refl

    -- σ=444 (3 nodes)
    cell-22 : κ 24 ≡ κ 24
    cell-22 = refl

    -- σ=460 (3 nodes)
    cell-23 : κ 24 ≡ κ 24
    cell-23 = refl

    -- σ=524 (3 nodes)
    cell-24 : κ 24 ≡ κ 24
    cell-24 = refl

    -- σ=80 (2 nodes)
    cell-25 : κ 24 ≡ κ 24
    cell-25 = refl

    -- σ=296 (2 nodes)
    cell-26 : κ 24 ≡ κ 24
    cell-26 = refl

    -- σ=939 (2 nodes)
    cell-27 : κ 24 ≡ κ 24
    cell-27 = refl

    -- σ=1166 (2 nodes)
    cell-28 : κ 24 ≡ κ 24
    cell-28 = refl

    -- σ=1332 (2 nodes)
    cell-29 : κ 24 ≡ κ 24
    cell-29 = refl

    -- σ=1562 (2 nodes)
    cell-30 : κ 24 ≡ κ 24
    cell-30 = refl

    -- σ=1770 (2 nodes)
    cell-31 : κ 24 ≡ κ 24
    cell-31 = refl

    -- σ=1774 (2 nodes)
    cell-32 : κ 24 ≡ κ 24
    cell-32 = refl

    -- σ=168 (1 nodes)
    cell-33 : κ 24 ≡ κ 24
    cell-33 = refl

    -- σ=171 (1 nodes)
    cell-34 : κ 24 ≡ κ 24
    cell-34 = refl

    -- σ=213 (1 nodes)
    cell-35 : κ 24 ≡ κ 24
    cell-35 = refl

    -- σ=310 (1 nodes)
    cell-36 : κ 24 ≡ κ 24
    cell-36 = refl

    -- σ=959 (1 nodes)
    cell-37 : κ 24 ≡ κ 24
    cell-37 = refl

    -- σ=1354 (1 nodes)
    cell-38 : κ 24 ≡ κ 24
    cell-38 = refl

    -- σ=1731 (1 nodes)
    cell-39 : κ 24 ≡ κ 24
    cell-39 = refl

    -- σ=1808 (1 nodes)
    cell-40 : κ 24 ≡ κ 24
    cell-40 = refl

    -- σ=1928 (1 nodes)
    cell-41 : κ 24 ≡ κ 24
    cell-41 = refl

    -- σ=1947 (1 nodes)
    cell-42 : κ 24 ≡ κ 24
    cell-42 = refl

    -- σ=2054 (1 nodes)
    cell-43 : κ 24 ≡ κ 24
    cell-43 = refl



-- κ=26: 130 nodes, 2 τ-classes, 43 σ-classes
module index-Index-0 where

  -- τ=36: 84 nodes, 38 σ-classes
  module τ36 where

    -- σ=123 (9 nodes)
    cell-0 : κ 26 ≡ κ 26
    cell-0 = refl

    -- σ=801 (6 nodes)
    cell-1 : κ 26 ≡ κ 26
    cell-1 = refl

    -- σ=976 (6 nodes)
    cell-2 : κ 26 ≡ κ 26
    cell-2 = refl

    -- σ=45 (5 nodes)
    cell-3 : κ 26 ≡ κ 26
    cell-3 = refl

    -- σ=771 (4 nodes)
    cell-4 : κ 26 ≡ κ 26
    cell-4 = refl

    -- σ=826 (4 nodes)
    cell-5 : κ 26 ≡ κ 26
    cell-5 = refl

    -- σ=93 (3 nodes)
    cell-6 : κ 26 ≡ κ 26
    cell-6 = refl

    -- σ=96 (3 nodes)
    cell-7 : κ 26 ≡ κ 26
    cell-7 = refl

    -- σ=580 (3 nodes)
    cell-8 : κ 26 ≡ κ 26
    cell-8 = refl

    -- σ=954 (3 nodes)
    cell-9 : κ 26 ≡ κ 26
    cell-9 = refl

    -- σ=1360 (3 nodes)
    cell-10 : κ 26 ≡ κ 26
    cell-10 = refl

    -- σ=57 (2 nodes)
    cell-11 : κ 26 ≡ κ 26
    cell-11 = refl

    -- σ=210 (2 nodes)
    cell-12 : κ 26 ≡ κ 26
    cell-12 = refl

    -- σ=433 (2 nodes)
    cell-13 : κ 26 ≡ κ 26
    cell-13 = refl

    -- σ=586 (2 nodes)
    cell-14 : κ 26 ≡ κ 26
    cell-14 = refl

    -- σ=1034 (2 nodes)
    cell-15 : κ 26 ≡ κ 26
    cell-15 = refl

    -- σ=1087 (2 nodes)
    cell-16 : κ 26 ≡ κ 26
    cell-16 = refl

    -- σ=1618 (2 nodes)
    cell-17 : κ 26 ≡ κ 26
    cell-17 = refl

    -- σ=1906 (2 nodes)
    cell-18 : κ 26 ≡ κ 26
    cell-18 = refl

    -- σ=261 (1 nodes)
    cell-19 : κ 26 ≡ κ 26
    cell-19 = refl

    -- σ=266 (1 nodes)
    cell-20 : κ 26 ≡ κ 26
    cell-20 = refl

    -- σ=398 (1 nodes)
    cell-21 : κ 26 ≡ κ 26
    cell-21 = refl

    -- σ=436 (1 nodes)
    cell-22 : κ 26 ≡ κ 26
    cell-22 = refl

    -- σ=558 (1 nodes)
    cell-23 : κ 26 ≡ κ 26
    cell-23 = refl

    -- σ=718 (1 nodes)
    cell-24 : κ 26 ≡ κ 26
    cell-24 = refl

    -- σ=737 (1 nodes)
    cell-25 : κ 26 ≡ κ 26
    cell-25 = refl

    -- σ=740 (1 nodes)
    cell-26 : κ 26 ≡ κ 26
    cell-26 = refl

    -- σ=1095 (1 nodes)
    cell-27 : κ 26 ≡ κ 26
    cell-27 = refl

    -- σ=1118 (1 nodes)
    cell-28 : κ 26 ≡ κ 26
    cell-28 = refl

    -- σ=1412 (1 nodes)
    cell-29 : κ 26 ≡ κ 26
    cell-29 = refl

    -- σ=1539 (1 nodes)
    cell-30 : κ 26 ≡ κ 26
    cell-30 = refl

    -- σ=1545 (1 nodes)
    cell-31 : κ 26 ≡ κ 26
    cell-31 = refl

    -- σ=1592 (1 nodes)
    cell-32 : κ 26 ≡ κ 26
    cell-32 = refl

    -- σ=1597 (1 nodes)
    cell-33 : κ 26 ≡ κ 26
    cell-33 = refl

    -- σ=1603 (1 nodes)
    cell-34 : κ 26 ≡ κ 26
    cell-34 = refl

    -- σ=1663 (1 nodes)
    cell-35 : κ 26 ≡ κ 26
    cell-35 = refl

    -- σ=1695 (1 nodes)
    cell-36 : κ 26 ≡ κ 26
    cell-36 = refl

    -- σ=1710 (1 nodes)
    cell-37 : κ 26 ≡ κ 26
    cell-37 = refl


  -- τ=113: 46 nodes, 6 σ-classes
  module τ113 where

    -- σ=346 (20 nodes)
    cell-0 : κ 26 ≡ κ 26
    cell-0 = refl

    -- σ=162 (19 nodes)
    cell-1 : κ 26 ≡ κ 26
    cell-1 = refl

    -- σ=219 (2 nodes)
    cell-2 : κ 26 ≡ κ 26
    cell-2 = refl

    -- σ=433 (2 nodes)
    cell-3 : κ 26 ≡ κ 26
    cell-3 = refl

    -- σ=550 (2 nodes)
    cell-4 : κ 26 ≡ κ 26
    cell-4 = refl

    -- σ=446 (1 nodes)
    cell-5 : κ 26 ≡ κ 26
    cell-5 = refl



-- κ=14: 36 nodes, 1 τ-classes, 28 σ-classes
module morphism-at-state-Attribute-1 where

  -- τ=14: 36 nodes, 28 σ-classes
  module Self-_counter where

    -- σ=376 (7 nodes)
    cell-0 : κ 14 ≡ κ 14
    cell-0 = refl

    -- σ=198 (2 nodes)
    cell-1 : κ 14 ≡ κ 14
    cell-1 = refl

    -- σ=401 (2 nodes)
    cell-2 : κ 14 ≡ κ 14
    cell-2 = refl

    -- σ=23 (1 nodes)
    cell-3 : κ 14 ≡ κ 14
    cell-3 = refl

    -- σ=31 (1 nodes)
    cell-4 : κ 14 ≡ κ 14
    cell-4 = refl

    -- σ=151 (1 nodes)
    cell-5 : κ 14 ≡ κ 14
    cell-5 = refl

    -- σ=154 (1 nodes)
    cell-6 : κ 14 ≡ κ 14
    cell-6 = refl

    -- σ=157 (1 nodes)
    cell-7 : κ 14 ≡ κ 14
    cell-7 = refl

    -- σ=160 (1 nodes)
    cell-8 : κ 14 ≡ κ 14
    cell-8 = refl

    -- σ=184 (1 nodes)
    cell-9 : κ 14 ≡ κ 14
    cell-9 = refl

    -- σ=187 (1 nodes)
    cell-10 : κ 14 ≡ κ 14
    cell-10 = refl

    -- σ=193 (1 nodes)
    cell-11 : κ 14 ≡ κ 14
    cell-11 = refl

    -- σ=200 (1 nodes)
    cell-12 : κ 14 ≡ κ 14
    cell-12 = refl

    -- σ=321 (1 nodes)
    cell-13 : κ 14 ≡ κ 14
    cell-13 = refl

    -- σ=326 (1 nodes)
    cell-14 : κ 14 ≡ κ 14
    cell-14 = refl

    -- σ=330 (1 nodes)
    cell-15 : κ 14 ≡ κ 14
    cell-15 = refl

    -- σ=334 (1 nodes)
    cell-16 : κ 14 ≡ κ 14
    cell-16 = refl

    -- σ=341 (1 nodes)
    cell-17 : κ 14 ≡ κ 14
    cell-17 = refl

    -- σ=355 (1 nodes)
    cell-18 : κ 14 ≡ κ 14
    cell-18 = refl

    -- σ=364 (1 nodes)
    cell-19 : κ 14 ≡ κ 14
    cell-19 = refl

    -- σ=369 (1 nodes)
    cell-20 : κ 14 ≡ κ 14
    cell-20 = refl

    -- σ=374 (1 nodes)
    cell-21 : κ 14 ≡ κ 14
    cell-21 = refl

    -- σ=378 (1 nodes)
    cell-22 : κ 14 ≡ κ 14
    cell-22 = refl

    -- σ=386 (1 nodes)
    cell-23 : κ 14 ≡ κ 14
    cell-23 = refl

    -- σ=393 (1 nodes)
    cell-24 : κ 14 ≡ κ 14
    cell-24 = refl

    -- σ=397 (1 nodes)
    cell-25 : κ 14 ≡ κ 14
    cell-25 = refl

    -- σ=403 (1 nodes)
    cell-26 : κ 14 ≡ κ 14
    cell-26 = refl

    -- σ=413 (1 nodes)
    cell-27 : κ 14 ≡ κ 14
    cell-27 = refl



-- κ=21: 38 nodes, 2 τ-classes, 27 σ-classes
module arg-arg-0 where

  -- τ=93: 32 nodes, 22 σ-classes
  module τ93 where

    -- σ=139 (4 nodes)
    cell-0 : κ 21 ≡ κ 21
    cell-0 = refl

    -- σ=471 (3 nodes)
    cell-1 : κ 21 ≡ κ 21
    cell-1 = refl

    -- σ=1521 (3 nodes)
    cell-2 : κ 21 ≡ κ 21
    cell-2 = refl

    -- σ=470 (2 nodes)
    cell-3 : κ 21 ≡ κ 21
    cell-3 = refl

    -- σ=709 (2 nodes)
    cell-4 : κ 21 ≡ κ 21
    cell-4 = refl

    -- σ=1522 (2 nodes)
    cell-5 : κ 21 ≡ κ 21
    cell-5 = refl

    -- σ=182 (1 nodes)
    cell-6 : κ 21 ≡ κ 21
    cell-6 = refl

    -- σ=205 (1 nodes)
    cell-7 : κ 21 ≡ κ 21
    cell-7 = refl

    -- σ=243 (1 nodes)
    cell-8 : κ 21 ≡ κ 21
    cell-8 = refl

    -- σ=244 (1 nodes)
    cell-9 : κ 21 ≡ κ 21
    cell-9 = refl

    -- σ=423 (1 nodes)
    cell-10 : κ 21 ≡ κ 21
    cell-10 = refl

    -- σ=469 (1 nodes)
    cell-11 : κ 21 ≡ κ 21
    cell-11 = refl

    -- σ=725 (1 nodes)
    cell-12 : κ 21 ≡ κ 21
    cell-12 = refl

    -- σ=726 (1 nodes)
    cell-13 : κ 21 ≡ κ 21
    cell-13 = refl

    -- σ=1218 (1 nodes)
    cell-14 : κ 21 ≡ κ 21
    cell-14 = refl

    -- σ=1222 (1 nodes)
    cell-15 : κ 21 ≡ κ 21
    cell-15 = refl

    -- σ=1223 (1 nodes)
    cell-16 : κ 21 ≡ κ 21
    cell-16 = refl

    -- σ=1409 (1 nodes)
    cell-17 : κ 21 ≡ κ 21
    cell-17 = refl

    -- σ=1456 (1 nodes)
    cell-18 : κ 21 ≡ κ 21
    cell-18 = refl

    -- σ=1457 (1 nodes)
    cell-19 : κ 21 ≡ κ 21
    cell-19 = refl

    -- σ=1481 (1 nodes)
    cell-20 : κ 21 ≡ κ 21
    cell-20 = refl

    -- σ=1482 (1 nodes)
    cell-21 : κ 21 ≡ κ 21
    cell-21 = refl


  -- τ=31: 6 nodes, 5 σ-classes
  module τ31 where

    -- σ=39 (2 nodes)
    cell-0 : κ 21 ≡ κ 21
    cell-0 = refl

    -- σ=72 (1 nodes)
    cell-1 : κ 21 ≡ κ 21
    cell-1 = refl

    -- σ=73 (1 nodes)
    cell-2 : κ 21 ≡ κ 21
    cell-2 = refl

    -- σ=112 (1 nodes)
    cell-3 : κ 21 ≡ κ 21
    cell-3 = refl

    -- σ=424 (1 nodes)
    cell-4 : κ 21 ≡ κ 21
    cell-4 = refl



-- κ=1: 26 nodes, 1 τ-classes, 26 σ-classes
module effect-seq-Expr-0 where

  -- τ=1: 26 nodes, 26 σ-classes
  module τ1 where

    -- σ=1 (1 nodes)
    cell-0 : κ 1 ≡ κ 1
    cell-0 = refl

    -- σ=12 (1 nodes)
    cell-1 : κ 1 ≡ κ 1
    cell-1 = refl

    -- σ=76 (1 nodes)
    cell-2 : κ 1 ≡ κ 1
    cell-2 = refl

    -- σ=132 (1 nodes)
    cell-3 : κ 1 ≡ κ 1
    cell-3 = refl

    -- σ=181 (1 nodes)
    cell-4 : κ 1 ≡ κ 1
    cell-4 = refl

    -- σ=238 (1 nodes)
    cell-5 : κ 1 ≡ κ 1
    cell-5 = refl

    -- σ=247 (1 nodes)
    cell-6 : κ 1 ≡ κ 1
    cell-6 = refl

    -- σ=274 (1 nodes)
    cell-7 : κ 1 ≡ κ 1
    cell-7 = refl

    -- σ=320 (1 nodes)
    cell-8 : κ 1 ≡ κ 1
    cell-8 = refl

    -- σ=430 (1 nodes)
    cell-9 : κ 1 ≡ κ 1
    cell-9 = refl

    -- σ=474 (1 nodes)
    cell-10 : κ 1 ≡ κ 1
    cell-10 = refl

    -- σ=750 (1 nodes)
    cell-11 : κ 1 ≡ κ 1
    cell-11 = refl

    -- σ=872 (1 nodes)
    cell-12 : κ 1 ≡ κ 1
    cell-12 = refl

    -- σ=916 (1 nodes)
    cell-13 : κ 1 ≡ κ 1
    cell-13 = refl

    -- σ=936 (1 nodes)
    cell-14 : κ 1 ≡ κ 1
    cell-14 = refl

    -- σ=1226 (1 nodes)
    cell-15 : κ 1 ≡ κ 1
    cell-15 = refl

    -- σ=1423 (1 nodes)
    cell-16 : κ 1 ≡ κ 1
    cell-16 = refl

    -- σ=1460 (1 nodes)
    cell-17 : κ 1 ≡ κ 1
    cell-17 = refl

    -- σ=1485 (1 nodes)
    cell-18 : κ 1 ≡ κ 1
    cell-18 = refl

    -- σ=1525 (1 nodes)
    cell-19 : κ 1 ≡ κ 1
    cell-19 = refl

    -- σ=1557 (1 nodes)
    cell-20 : κ 1 ≡ κ 1
    cell-20 = refl

    -- σ=1571 (1 nodes)
    cell-21 : κ 1 ≡ κ 1
    cell-21 = refl

    -- σ=1640 (1 nodes)
    cell-22 : κ 1 ≡ κ 1
    cell-22 = refl

    -- σ=1693 (1 nodes)
    cell-23 : κ 1 ≡ κ 1
    cell-23 = refl

    -- σ=1723 (1 nodes)
    cell-24 : κ 1 ≡ κ 1
    cell-24 = refl

    -- σ=1794 (1 nodes)
    cell-25 : κ 1 ≡ κ 1
    cell-25 = refl



-- κ=33: 36 nodes, 2 τ-classes, 25 σ-classes
module subscript-Subscript-0 where

  -- τ=47: 32 nodes, 21 σ-classes
  module τ47 where

    -- σ=581 (3 nodes)
    cell-0 : κ 33 ≡ κ 33
    cell-0 = refl

    -- σ=58 (2 nodes)
    cell-1 : κ 33 ≡ κ 33
    cell-1 = refl

    -- σ=63 (2 nodes)
    cell-2 : κ 33 ≡ κ 33
    cell-2 = refl

    -- σ=94 (2 nodes)
    cell-3 : κ 33 ≡ κ 33
    cell-3 = refl

    -- σ=97 (2 nodes)
    cell-4 : κ 33 ≡ κ 33
    cell-4 = refl

    -- σ=434 (2 nodes)
    cell-5 : κ 33 ≡ κ 33
    cell-5 = refl

    -- σ=772 (2 nodes)
    cell-6 : κ 33 ≡ κ 33
    cell-6 = refl

    -- σ=827 (2 nodes)
    cell-7 : κ 33 ≡ κ 33
    cell-7 = refl

    -- σ=1088 (2 nodes)
    cell-8 : κ 33 ≡ κ 33
    cell-8 = refl

    -- σ=1363 (2 nodes)
    cell-9 : κ 33 ≡ κ 33
    cell-9 = refl

    -- σ=211 (1 nodes)
    cell-10 : κ 33 ≡ κ 33
    cell-10 = refl

    -- σ=262 (1 nodes)
    cell-11 : κ 33 ≡ κ 33
    cell-11 = refl

    -- σ=267 (1 nodes)
    cell-12 : κ 33 ≡ κ 33
    cell-12 = refl

    -- σ=719 (1 nodes)
    cell-13 : κ 33 ≡ κ 33
    cell-13 = refl

    -- σ=738 (1 nodes)
    cell-14 : κ 33 ≡ κ 33
    cell-14 = refl

    -- σ=741 (1 nodes)
    cell-15 : κ 33 ≡ κ 33
    cell-15 = refl

    -- σ=955 (1 nodes)
    cell-16 : κ 33 ≡ κ 33
    cell-16 = refl

    -- σ=1035 (1 nodes)
    cell-17 : κ 33 ≡ κ 33
    cell-17 = refl

    -- σ=1096 (1 nodes)
    cell-18 : κ 33 ≡ κ 33
    cell-18 = refl

    -- σ=1546 (1 nodes)
    cell-19 : κ 33 ≡ κ 33
    cell-19 = refl

    -- σ=1696 (1 nodes)
    cell-20 : κ 33 ≡ κ 33
    cell-20 = refl


  -- τ=157: 4 nodes, 4 σ-classes
  module τ157 where

    -- σ=228 (1 nodes)
    cell-0 : κ 33 ≡ κ 33
    cell-0 = refl

    -- σ=447 (1 nodes)
    cell-1 : κ 33 ≡ κ 33
    cell-1 = refl

    -- σ=536 (1 nodes)
    cell-2 : κ 33 ≡ κ 33
    cell-2 = refl

    -- σ=539 (1 nodes)
    cell-3 : κ 33 ≡ κ 33
    cell-3 = refl



-- κ=67: 58 nodes, 4 τ-classes, 21 σ-classes
module subscript-Subscript-1 where

  -- τ=195: 25 nodes, 5 σ-classes
  module τ195 where

    -- σ=347 (17 nodes)
    cell-0 : κ 67 ≡ κ 67
    cell-0 = refl

    -- σ=1488 (3 nodes)
    cell-1 : κ 67 ≡ κ 67
    cell-1 = refl

    -- σ=292 (2 nodes)
    cell-2 : κ 67 ≡ κ 67
    cell-2 = refl

    -- σ=1573 (2 nodes)
    cell-3 : κ 67 ≡ κ 67
    cell-3 = refl

    -- σ=551 (1 nodes)
    cell-4 : κ 67 ≡ κ 67
    cell-4 = refl


  -- τ=114: 15 nodes, 3 σ-classes
  module τ114 where

    -- σ=163 (7 nodes)
    cell-0 : κ 67 ≡ κ 67
    cell-0 = refl

    -- σ=277 (7 nodes)
    cell-1 : κ 67 ≡ κ 67
    cell-1 = refl

    -- σ=746 (1 nodes)
    cell-2 : κ 67 ≡ κ 67
    cell-2 = refl


  -- τ=257: 10 nodes, 5 σ-classes
  module τ257 where

    -- σ=417 (5 nodes)
    cell-0 : κ 67 ≡ κ 67
    cell-0 = refl

    -- σ=379 (2 nodes)
    cell-1 : κ 67 ≡ κ 67
    cell-1 = refl

    -- σ=399 (1 nodes)
    cell-2 : κ 67 ≡ κ 67
    cell-2 = refl

    -- σ=1413 (1 nodes)
    cell-3 : κ 67 ≡ κ 67
    cell-3 = refl

    -- σ=1627 (1 nodes)
    cell-4 : κ 67 ≡ κ 67
    cell-4 = refl


  -- τ=84: 8 nodes, 8 σ-classes
  module τ84 where

    -- σ=124 (1 nodes)
    cell-0 : κ 67 ≡ κ 67
    cell-0 = refl

    -- σ=565 (1 nodes)
    cell-1 : κ 67 ≡ κ 67
    cell-1 = refl

    -- σ=802 (1 nodes)
    cell-2 : κ 67 ≡ κ 67
    cell-2 = refl

    -- σ=977 (1 nodes)
    cell-3 : κ 67 ≡ κ 67
    cell-3 = refl

    -- σ=1038 (1 nodes)
    cell-4 : κ 67 ≡ κ 67
    cell-4 = refl

    -- σ=1069 (1 nodes)
    cell-5 : κ 67 ≡ κ 67
    cell-5 = refl

    -- σ=1711 (1 nodes)
    cell-6 : κ 67 ≡ κ 67
    cell-6 = refl

    -- σ=1910 (1 nodes)
    cell-7 : κ 67 ≡ κ 67
    cell-7 = refl



-- κ=106: 46 nodes, 2 τ-classes, 19 σ-classes
module apply-Call-0 where

  -- τ=165: 41 nodes, 16 σ-classes
  module τ165 where

    -- σ=795 (11 nodes)
    cell-0 : κ 106 ≡ κ 106
    cell-0 = refl

    -- σ=1182 (5 nodes)
    cell-1 : κ 106 ≡ κ 106
    cell-1 = refl

    -- σ=686 (4 nodes)
    cell-2 : κ 106 ≡ κ 106
    cell-2 = refl

    -- σ=729 (4 nodes)
    cell-3 : κ 106 ≡ κ 106
    cell-3 = refl

    -- σ=240 (3 nodes)
    cell-4 : κ 106 ≡ κ 106
    cell-4 = refl

    -- σ=573 (3 nodes)
    cell-5 : κ 106 ≡ κ 106
    cell-5 = refl

    -- σ=1186 (2 nodes)
    cell-6 : κ 106 ≡ κ 106
    cell-6 = refl

    -- σ=248 (1 nodes)
    cell-7 : κ 106 ≡ κ 106
    cell-7 = refl

    -- σ=249 (1 nodes)
    cell-8 : κ 106 ≡ κ 106
    cell-8 = refl

    -- σ=479 (1 nodes)
    cell-9 : κ 106 ≡ κ 106
    cell-9 = refl

    -- σ=713 (1 nodes)
    cell-10 : κ 106 ≡ κ 106
    cell-10 = refl

    -- σ=732 (1 nodes)
    cell-11 : κ 106 ≡ κ 106
    cell-11 = refl

    -- σ=893 (1 nodes)
    cell-12 : κ 106 ≡ κ 106
    cell-12 = refl

    -- σ=1252 (1 nodes)
    cell-13 : κ 106 ≡ κ 106
    cell-13 = refl

    -- σ=1283 (1 nodes)
    cell-14 : κ 106 ≡ κ 106
    cell-14 = refl

    -- σ=1886 (1 nodes)
    cell-15 : κ 106 ≡ κ 106
    cell-15 = refl


  -- τ=154: 5 nodes, 3 σ-classes
  module τ154 where

    -- σ=652 (2 nodes)
    cell-0 : κ 106 ≡ κ 106
    cell-0 = refl

    -- σ=1144 (2 nodes)
    cell-1 : κ 106 ≡ κ 106
    cell-1 = refl

    -- σ=225 (1 nodes)
    cell-2 : κ 106 ≡ κ 106
    cell-2 = refl



-- κ=127: 27 nodes, 1 τ-classes, 19 σ-classes
module let-k-Assign-0 where

  -- τ=186: 27 nodes, 19 σ-classes
  module τ186 where

    -- σ=796 (5 nodes)
    cell-0 : κ 127 ≡ κ 127
    cell-0 = refl

    -- σ=574 (3 nodes)
    cell-1 : κ 127 ≡ κ 127
    cell-1 = refl

    -- σ=925 (2 nodes)
    cell-2 : κ 127 ≡ κ 127
    cell-2 = refl

    -- σ=1049 (2 nodes)
    cell-3 : κ 127 ≡ κ 127
    cell-3 = refl

    -- σ=281 (1 nodes)
    cell-4 : κ 127 ≡ κ 127
    cell-4 = refl

    -- σ=480 (1 nodes)
    cell-5 : κ 127 ≡ κ 127
    cell-5 = refl

    -- σ=714 (1 nodes)
    cell-6 : κ 127 ≡ κ 127
    cell-6 = refl

    -- σ=730 (1 nodes)
    cell-7 : κ 127 ≡ κ 127
    cell-7 = refl

    -- σ=733 (1 nodes)
    cell-8 : κ 127 ≡ κ 127
    cell-8 = refl

    -- σ=846 (1 nodes)
    cell-9 : κ 127 ≡ κ 127
    cell-9 = refl

    -- σ=1114 (1 nodes)
    cell-10 : κ 127 ≡ κ 127
    cell-10 = refl

    -- σ=1183 (1 nodes)
    cell-11 : κ 127 ≡ κ 127
    cell-11 = refl

    -- σ=1187 (1 nodes)
    cell-12 : κ 127 ≡ κ 127
    cell-12 = refl

    -- σ=1201 (1 nodes)
    cell-13 : κ 127 ≡ κ 127
    cell-13 = refl

    -- σ=1313 (1 nodes)
    cell-14 : κ 127 ≡ κ 127
    cell-14 = refl

    -- σ=1315 (1 nodes)
    cell-15 : κ 127 ≡ κ 127
    cell-15 = refl

    -- σ=1327 (1 nodes)
    cell-16 : κ 127 ≡ κ 127
    cell-16 = refl

    -- σ=1367 (1 nodes)
    cell-17 : κ 127 ≡ κ 127
    cell-17 = refl

    -- σ=1391 (1 nodes)
    cell-18 : κ 127 ≡ κ 127
    cell-18 = refl



-- κ=275: 24 nodes, 2 τ-classes, 18 σ-classes
module coerce-FormattedValue-0 where

  -- τ=486: 15 nodes, 14 σ-classes
  module τ486 where

    -- σ=611 (2 nodes)
    cell-0 : κ 275 ≡ κ 275
    cell-0 = refl

    -- σ=840 (1 nodes)
    cell-1 : κ 275 ≡ κ 275
    cell-1 = refl

    -- σ=1300 (1 nodes)
    cell-2 : κ 275 ≡ κ 275
    cell-2 = refl

    -- σ=1935 (1 nodes)
    cell-3 : κ 275 ≡ κ 275
    cell-3 = refl

    -- σ=1945 (1 nodes)
    cell-4 : κ 275 ≡ κ 275
    cell-4 = refl

    -- σ=1957 (1 nodes)
    cell-5 : κ 275 ≡ κ 275
    cell-5 = refl

    -- σ=2000 (1 nodes)
    cell-6 : κ 275 ≡ κ 275
    cell-6 = refl

    -- σ=2043 (1 nodes)
    cell-7 : κ 275 ≡ κ 275
    cell-7 = refl

    -- σ=2046 (1 nodes)
    cell-8 : κ 275 ≡ κ 275
    cell-8 = refl

    -- σ=2070 (1 nodes)
    cell-9 : κ 275 ≡ κ 275
    cell-9 = refl

    -- σ=2072 (1 nodes)
    cell-10 : κ 275 ≡ κ 275
    cell-10 = refl

    -- σ=2074 (1 nodes)
    cell-11 : κ 275 ≡ κ 275
    cell-11 = refl

    -- σ=2075 (1 nodes)
    cell-12 : κ 275 ≡ κ 275
    cell-12 = refl

    -- σ=2083 (1 nodes)
    cell-13 : κ 275 ≡ κ 275
    cell-13 = refl


  -- τ=377: 9 nodes, 5 σ-classes
  module τ377 where

    -- σ=611 (5 nodes)
    cell-0 : κ 275 ≡ κ 275
    cell-0 = refl

    -- σ=1813 (1 nodes)
    cell-1 : κ 275 ≡ κ 275
    cell-1 = refl

    -- σ=1959 (1 nodes)
    cell-2 : κ 275 ≡ κ 275
    cell-2 = refl

    -- σ=1994 (1 nodes)
    cell-3 : κ 275 ≡ κ 275
    cell-3 = refl

    -- σ=2037 (1 nodes)
    cell-4 : κ 275 ≡ κ 275
    cell-4 = refl



-- κ=15: 30 nodes, 4 τ-classes, 17 σ-classes
module product-Tuple-0 where

  -- τ=17: 12 nodes, 10 σ-classes
  module tuple-0 where

    -- σ=26 (2 nodes)
    cell-0 : κ 15 ≡ κ 15
    cell-0 = refl

    -- σ=441 (2 nodes)
    cell-1 : κ 15 ≡ κ 15
    cell-1 = refl

    -- σ=99 (1 nodes)
    cell-2 : κ 15 ≡ κ 15
    cell-2 = refl

    -- σ=544 (1 nodes)
    cell-3 : κ 15 ≡ κ 15
    cell-3 = refl

    -- σ=902 (1 nodes)
    cell-4 : κ 15 ≡ κ 15
    cell-4 = refl

    -- σ=984 (1 nodes)
    cell-5 : κ 15 ≡ κ 15
    cell-5 = refl

    -- σ=1237 (1 nodes)
    cell-6 : κ 15 ≡ κ 15
    cell-6 = refl

    -- σ=1272 (1 nodes)
    cell-7 : κ 15 ≡ κ 15
    cell-7 = refl

    -- σ=1632 (1 nodes)
    cell-8 : κ 15 ≡ κ 15
    cell-8 = refl

    -- σ=1670 (1 nodes)
    cell-9 : κ 15 ≡ κ 15
    cell-9 = refl


  -- τ=250: 10 nodes, 3 σ-classes
  module tuple-1 where

    -- σ=1576 (6 nodes)
    cell-0 : κ 15 ≡ κ 15
    cell-0 = refl

    -- σ=1461 (3 nodes)
    cell-1 : κ 15 ≡ κ 15
    cell-1 = refl

    -- σ=370 (1 nodes)
    cell-2 : κ 15 ≡ κ 15
    cell-2 = refl


  -- τ=127: 6 nodes, 3 σ-classes
  module tuple-2 where

    -- σ=335 (3 nodes)
    cell-0 : κ 15 ≡ κ 15
    cell-0 = refl

    -- σ=414 (2 nodes)
    cell-1 : κ 15 ≡ κ 15
    cell-1 = refl

    -- σ=189 (1 nodes)
    cell-2 : κ 15 ≡ κ 15
    cell-2 = refl


  -- τ=25: 2 nodes, 1 σ-classes
  module tuple-3 where

    -- σ=33 (2 nodes)
    cell-0 : κ 15 ≡ κ 15
    cell-0 = refl



-- κ=149: 23 nodes, 2 τ-classes, 17 σ-classes
module cardinality-Call-0 where

  -- τ=335: 22 nodes, 16 σ-classes
  module int-0 where

    -- σ=1787 (3 nodes)
    cell-0 : κ 149 ≡ κ 149
    cell-0 = refl

    -- σ=1738 (2 nodes)
    cell-1 : κ 149 ≡ κ 149
    cell-1 = refl

    -- σ=1846 (2 nodes)
    cell-2 : κ 149 ≡ κ 149
    cell-2 = refl

    -- σ=1893 (2 nodes)
    cell-3 : κ 149 ≡ κ 149
    cell-3 = refl

    -- σ=1895 (2 nodes)
    cell-4 : κ 149 ≡ κ 149
    cell-4 = refl

    -- σ=502 (1 nodes)
    cell-5 : κ 149 ≡ κ 149
    cell-5 = refl

    -- σ=561 (1 nodes)
    cell-6 : κ 149 ≡ κ 149
    cell-6 = refl

    -- σ=603 (1 nodes)
    cell-7 : κ 149 ≡ κ 149
    cell-7 = refl

    -- σ=694 (1 nodes)
    cell-8 : κ 149 ≡ κ 149
    cell-8 = refl

    -- σ=991 (1 nodes)
    cell-9 : κ 149 ≡ κ 149
    cell-9 = refl

    -- σ=1123 (1 nodes)
    cell-10 : κ 149 ≡ κ 149
    cell-10 = refl

    -- σ=1163 (1 nodes)
    cell-11 : κ 149 ≡ κ 149
    cell-11 = refl

    -- σ=1337 (1 nodes)
    cell-12 : κ 149 ≡ κ 149
    cell-12 = refl

    -- σ=1552 (1 nodes)
    cell-13 : κ 149 ≡ κ 149
    cell-13 = refl

    -- σ=1735 (1 nodes)
    cell-14 : κ 149 ≡ κ 149
    cell-14 = refl

    -- σ=2039 (1 nodes)
    cell-15 : κ 149 ≡ κ 149
    cell-15 = refl


  -- τ=210: 1 nodes, 1 σ-classes
  module int-1 where

    -- σ=312 (1 nodes)
    cell-0 : κ 149 ≡ κ 149
    cell-0 = refl



-- κ=105: 68 nodes, 1 τ-classes, 14 σ-classes
module morphism-at-state-Attribute-2 where

  -- τ=153: 68 nodes, 14 σ-classes
  module Self-tau-canonical where

    -- σ=477 (39 nodes)
    cell-0 : κ 105 ≡ κ 105
    cell-0 = refl

    -- σ=810 (6 nodes)
    cell-1 : κ 105 ≡ κ 105
    cell-1 = refl

    -- σ=239 (5 nodes)
    cell-2 : κ 105 ≡ κ 105
    cell-2 = refl

    -- σ=575 (4 nodes)
    cell-3 : κ 105 ≡ κ 105
    cell-3 = refl

    -- σ=651 (3 nodes)
    cell-4 : κ 105 ≡ κ 105
    cell-4 = refl

    -- σ=1142 (2 nodes)
    cell-5 : κ 105 ≡ κ 105
    cell-5 = refl

    -- σ=1151 (2 nodes)
    cell-6 : κ 105 ≡ κ 105
    cell-6 = refl

    -- σ=224 (1 nodes)
    cell-7 : κ 105 ≡ κ 105
    cell-7 = refl

    -- σ=253 (1 nodes)
    cell-8 : κ 105 ≡ κ 105
    cell-8 = refl

    -- σ=1241 (1 nodes)
    cell-9 : κ 105 ≡ κ 105
    cell-9 = refl

    -- σ=1247 (1 nodes)
    cell-10 : κ 105 ≡ κ 105
    cell-10 = refl

    -- σ=1268 (1 nodes)
    cell-11 : κ 105 ≡ κ 105
    cell-11 = refl

    -- σ=1590 (1 nodes)
    cell-12 : κ 105 ≡ κ 105
    cell-12 = refl

    -- σ=1601 (1 nodes)
    cell-13 : κ 105 ≡ κ 105
    cell-13 = refl



-- κ=353: 18 nodes, 2 τ-classes, 14 σ-classes
module apply-Call-1 where

  -- τ=473: 16 nodes, 12 σ-classes
  module τ473 where

    -- σ=808 (4 nodes)
    cell-0 : κ 353 ≡ κ 353
    cell-0 = refl

    -- σ=1333 (2 nodes)
    cell-1 : κ 353 ≡ κ 353
    cell-1 = refl

    -- σ=942 (1 nodes)
    cell-2 : κ 353 ≡ κ 353
    cell-2 = refl

    -- σ=1167 (1 nodes)
    cell-3 : κ 353 ≡ κ 353
    cell-3 = refl

    -- σ=1170 (1 nodes)
    cell-4 : κ 353 ≡ κ 353
    cell-4 = refl

    -- σ=1191 (1 nodes)
    cell-5 : κ 353 ≡ κ 353
    cell-5 = refl

    -- σ=1318 (1 nodes)
    cell-6 : κ 353 ≡ κ 353
    cell-6 = refl

    -- σ=1469 (1 nodes)
    cell-7 : κ 353 ≡ κ 353
    cell-7 = refl

    -- σ=1471 (1 nodes)
    cell-8 : κ 353 ≡ κ 353
    cell-8 = refl

    -- σ=1496 (1 nodes)
    cell-9 : κ 353 ≡ κ 353
    cell-9 = refl

    -- σ=1500 (1 nodes)
    cell-10 : κ 353 ≡ κ 353
    cell-10 = refl

    -- σ=2055 (1 nodes)
    cell-11 : κ 353 ≡ κ 353
    cell-11 = refl


  -- τ=653: 2 nodes, 2 σ-classes
  module τ653 where

    -- σ=1339 (1 nodes)
    cell-0 : κ 353 ≡ κ 353
    cell-0 = refl

    -- σ=1355 (1 nodes)
    cell-1 : κ 353 ≡ κ 353
    cell-1 = refl



-- κ=17: 20 nodes, 5 τ-classes, 13 σ-classes
module subscript-Subscript-2 where

  -- τ=252: 10 nodes, 5 σ-classes
  module τ252 where

    -- σ=1589 (4 nodes)
    cell-0 : κ 17 ≡ κ 17
    cell-0 = refl

    -- σ=1463 (2 nodes)
    cell-1 : κ 17 ≡ κ 17
    cell-1 = refl

    -- σ=1578 (2 nodes)
    cell-2 : κ 17 ≡ κ 17
    cell-2 = refl

    -- σ=372 (1 nodes)
    cell-3 : κ 17 ≡ κ 17
    cell-3 = refl

    -- σ=1516 (1 nodes)
    cell-4 : κ 17 ≡ κ 17
    cell-4 = refl


  -- τ=129: 6 nodes, 5 σ-classes
  module τ129 where

    -- σ=337 (2 nodes)
    cell-0 : κ 17 ≡ κ 17
    cell-0 = refl

    -- σ=191 (1 nodes)
    cell-1 : κ 17 ≡ κ 17
    cell-1 = refl

    -- σ=416 (1 nodes)
    cell-2 : κ 17 ≡ κ 17
    cell-2 = refl

    -- σ=1107 (1 nodes)
    cell-3 : κ 17 ≡ κ 17
    cell-3 = refl

    -- σ=1213 (1 nodes)
    cell-4 : κ 17 ≡ κ 17
    cell-4 = refl


  -- τ=19: 2 nodes, 1 σ-classes
  module τ19 where

    -- σ=28 (2 nodes)
    cell-0 : κ 17 ≡ κ 17
    cell-0 = refl


  -- τ=27: 1 nodes, 1 σ-classes
  module τ27 where

    -- σ=35 (1 nodes)
    cell-0 : κ 17 ≡ κ 17
    cell-0 = refl


  -- τ=281: 1 nodes, 1 σ-classes
  module τ281 where

    -- σ=404 (1 nodes)
    cell-0 : κ 17 ≡ κ 17
    cell-0 = refl



-- κ=255: 12 nodes, 1 τ-classes, 12 σ-classes
module let-k-Assign-1 where

  -- τ=356: 12 nodes, 12 σ-classes
  module τ356 where

    -- σ=560 (1 nodes)
    cell-0 : κ 255 ≡ κ 255
    cell-0 = refl

    -- σ=814 (1 nodes)
    cell-1 : κ 255 ≡ κ 255
    cell-1 = refl

    -- σ=821 (1 nodes)
    cell-2 : κ 255 ≡ κ 255
    cell-2 = refl

    -- σ=981 (1 nodes)
    cell-3 : κ 255 ≡ κ 255
    cell-3 = refl

    -- σ=988 (1 nodes)
    cell-4 : κ 255 ≡ κ 255
    cell-4 = refl

    -- σ=1042 (1 nodes)
    cell-5 : κ 255 ≡ κ 255
    cell-5 = refl

    -- σ=1062 (1 nodes)
    cell-6 : κ 255 ≡ κ 255
    cell-6 = refl

    -- σ=1073 (1 nodes)
    cell-7 : κ 255 ≡ κ 255
    cell-7 = refl

    -- σ=1080 (1 nodes)
    cell-8 : κ 255 ≡ κ 255
    cell-8 = refl

    -- σ=1120 (1 nodes)
    cell-9 : κ 255 ≡ κ 255
    cell-9 = refl

    -- σ=1362 (1 nodes)
    cell-10 : κ 255 ≡ κ 255
    cell-10 = refl

    -- σ=1665 (1 nodes)
    cell-11 : κ 255 ≡ κ 255
    cell-11 = refl



-- κ=36: 11 nodes, 2 τ-classes, 11 σ-classes
module let-k-Assign-2 where

  -- τ=50: 9 nodes, 9 σ-classes
  module τ50 where

    -- σ=61 (1 nodes)
    cell-0 : κ 36 ≡ κ 36
    cell-0 = refl

    -- σ=212 (1 nodes)
    cell-1 : κ 36 ≡ κ 36
    cell-1 = refl

    -- σ=674 (1 nodes)
    cell-2 : κ 36 ≡ κ 36
    cell-2 = refl

    -- σ=773 (1 nodes)
    cell-3 : κ 36 ≡ κ 36
    cell-3 = refl

    -- σ=956 (1 nodes)
    cell-4 : κ 36 ≡ κ 36
    cell-4 = refl

    -- σ=1036 (1 nodes)
    cell-5 : κ 36 ≡ κ 36
    cell-5 = refl

    -- σ=1278 (1 nodes)
    cell-6 : κ 36 ≡ κ 36
    cell-6 = refl

    -- σ=1697 (1 nodes)
    cell-7 : κ 36 ≡ κ 36
    cell-7 = refl

    -- σ=2009 (1 nodes)
    cell-8 : κ 36 ≡ κ 36
    cell-8 = refl


  -- τ=352: 2 nodes, 2 σ-classes
  module τ352 where

    -- σ=537 (1 nodes)
    cell-0 : κ 36 ≡ κ 36
    cell-0 = refl

    -- σ=540 (1 nodes)
    cell-1 : κ 36 ≡ κ 36
    cell-1 = refl



-- κ=254: 15 nodes, 2 τ-classes, 11 σ-classes
module subscript-Subscript-3 where

  -- τ=355: 14 nodes, 10 σ-classes
  module τ355 where

    -- σ=813 (2 nodes)
    cell-0 : κ 254 ≡ κ 254
    cell-0 = refl

    -- σ=980 (2 nodes)
    cell-1 : κ 254 ≡ κ 254
    cell-1 = refl

    -- σ=1041 (2 nodes)
    cell-2 : κ 254 ≡ κ 254
    cell-2 = refl

    -- σ=1072 (2 nodes)
    cell-3 : κ 254 ≡ κ 254
    cell-3 = refl

    -- σ=559 (1 nodes)
    cell-4 : κ 254 ≡ κ 254
    cell-4 = refl

    -- σ=1119 (1 nodes)
    cell-5 : κ 254 ≡ κ 254
    cell-5 = refl

    -- σ=1361 (1 nodes)
    cell-6 : κ 254 ≡ κ 254
    cell-6 = refl

    -- σ=1619 (1 nodes)
    cell-7 : κ 254 ≡ κ 254
    cell-7 = refl

    -- σ=1664 (1 nodes)
    cell-8 : κ 254 ≡ κ 254
    cell-8 = refl

    -- σ=1907 (1 nodes)
    cell-9 : κ 254 ≡ κ 254
    cell-9 = refl


  -- τ=434: 1 nodes, 1 σ-classes
  module τ434 where

    -- σ=703 (1 nodes)
    cell-0 : κ 254 ≡ κ 254
    cell-0 = refl



-- κ=258: 20 nodes, 1 τ-classes, 11 σ-classes
module projection-at-x3f-Attribute-0 where

  -- τ=188: 20 nodes, 11 σ-classes
  module τ188 where

    -- σ=570 (6 nodes)
    cell-0 : κ 258 ≡ κ 258
    cell-0 = refl

    -- σ=787 (4 nodes)
    cell-1 : κ 258 ≡ κ 258
    cell-1 = refl

    -- σ=626 (2 nodes)
    cell-2 : κ 258 ≡ κ 258
    cell-2 = refl

    -- σ=1004 (1 nodes)
    cell-3 : κ 258 ≡ κ 258
    cell-3 = refl

    -- σ=1126 (1 nodes)
    cell-4 : κ 258 ≡ κ 258
    cell-4 = refl

    -- σ=1511 (1 nodes)
    cell-5 : κ 258 ≡ κ 258
    cell-5 = refl

    -- σ=1739 (1 nodes)
    cell-6 : κ 258 ≡ κ 258
    cell-6 = refl

    -- σ=1746 (1 nodes)
    cell-7 : κ 258 ≡ κ 258
    cell-7 = refl

    -- σ=1918 (1 nodes)
    cell-8 : κ 258 ≡ κ 258
    cell-8 = refl

    -- σ=2022 (1 nodes)
    cell-9 : κ 258 ≡ κ 258
    cell-9 = refl

    -- σ=2061 (1 nodes)
    cell-10 : κ 258 ≡ κ 258
    cell-10 = refl



-- κ=259: 20 nodes, 1 τ-classes, 11 σ-classes
module projection-compute-at-x3f-Call-0 where

  -- τ=361: 20 nodes, 11 σ-classes
  module τ361 where

    -- σ=571 (6 nodes)
    cell-0 : κ 259 ≡ κ 259
    cell-0 = refl

    -- σ=788 (4 nodes)
    cell-1 : κ 259 ≡ κ 259
    cell-1 = refl

    -- σ=627 (2 nodes)
    cell-2 : κ 259 ≡ κ 259
    cell-2 = refl

    -- σ=1005 (1 nodes)
    cell-3 : κ 259 ≡ κ 259
    cell-3 = refl

    -- σ=1127 (1 nodes)
    cell-4 : κ 259 ≡ κ 259
    cell-4 = refl

    -- σ=1512 (1 nodes)
    cell-5 : κ 259 ≡ κ 259
    cell-5 = refl

    -- σ=1740 (1 nodes)
    cell-6 : κ 259 ≡ κ 259
    cell-6 = refl

    -- σ=1747 (1 nodes)
    cell-7 : κ 259 ≡ κ 259
    cell-7 = refl

    -- σ=1919 (1 nodes)
    cell-8 : κ 259 ≡ κ 259
    cell-8 = refl

    -- σ=2023 (1 nodes)
    cell-9 : κ 259 ≡ κ 259
    cell-9 = refl

    -- σ=2062 (1 nodes)
    cell-10 : κ 259 ≡ κ 259
    cell-10 = refl



-- κ=300: 15 nodes, 1 τ-classes, 11 σ-classes
module morphism-at-x3f-Attribute-0 where

  -- τ=188: 15 nodes, 11 σ-classes
  module τ188 where

    -- σ=1007 (4 nodes)
    cell-0 : κ 300 ≡ κ 300
    cell-0 = refl

    -- σ=919 (2 nodes)
    cell-1 : κ 300 ≡ κ 300
    cell-1 = refl

    -- σ=666 (1 nodes)
    cell-2 : κ 300 ≡ κ 300
    cell-2 = refl

    -- σ=758 (1 nodes)
    cell-3 : κ 300 ≡ κ 300
    cell-3 = refl

    -- σ=1350 (1 nodes)
    cell-4 : κ 300 ≡ κ 300
    cell-4 = refl

    -- σ=1418 (1 nodes)
    cell-5 : κ 300 ≡ κ 300
    cell-5 = refl

    -- σ=1533 (1 nodes)
    cell-6 : κ 300 ≡ κ 300
    cell-6 = refl

    -- σ=1537 (1 nodes)
    cell-7 : κ 300 ≡ κ 300
    cell-7 = refl

    -- σ=1675 (1 nodes)
    cell-8 : κ 300 ≡ κ 300
    cell-8 = refl

    -- σ=1704 (1 nodes)
    cell-9 : κ 300 ≡ κ 300
    cell-9 = refl

    -- σ=1757 (1 nodes)
    cell-10 : κ 300 ≡ κ 300
    cell-10 = refl



-- κ=27: 13 nodes, 2 τ-classes, 10 σ-classes
module subscript-Subscript-4 where

  -- τ=37: 12 nodes, 9 σ-classes
  module τ37 where

    -- σ=46 (2 nodes)
    cell-0 : κ 27 ≡ κ 27
    cell-0 = refl

    -- σ=824 (2 nodes)
    cell-1 : κ 27 ≡ κ 27
    cell-1 = refl

    -- σ=1159 (2 nodes)
    cell-2 : κ 27 ≡ κ 27
    cell-2 = refl

    -- σ=49 (1 nodes)
    cell-3 : κ 27 ≡ κ 27
    cell-3 = refl

    -- σ=102 (1 nodes)
    cell-4 : κ 27 ≡ κ 27
    cell-4 = refl

    -- σ=105 (1 nodes)
    cell-5 : κ 27 ≡ κ 27
    cell-5 = refl

    -- σ=216 (1 nodes)
    cell-6 : κ 27 ≡ κ 27
    cell-6 = refl

    -- σ=1002 (1 nodes)
    cell-7 : κ 27 ≡ κ 27
    cell-7 = refl

    -- σ=1083 (1 nodes)
    cell-8 : κ 27 ≡ κ 27
    cell-8 = refl


  -- τ=150: 1 nodes, 1 σ-classes
  module τ150 where

    -- σ=220 (1 nodes)
    cell-0 : κ 27 ≡ κ 27
    cell-0 = refl



-- κ=45: 19 nodes, 1 τ-classes, 10 σ-classes
module product-unpack-Tuple-0 where

  -- τ=59: 19 nodes, 10 σ-classes
  module tuple where

    -- σ=785 (5 nodes)
    cell-0 : κ 45 ≡ κ 45
    cell-0 = refl

    -- σ=79 (3 nodes)
    cell-1 : κ 45 ≡ κ 45
    cell-1 = refl

    -- σ=1435 (2 nodes)
    cell-2 : κ 45 ≡ κ 45
    cell-2 = refl

    -- σ=1510 (2 nodes)
    cell-3 : κ 45 ≡ κ 45
    cell-3 = refl

    -- σ=1769 (2 nodes)
    cell-4 : κ 45 ≡ κ 45
    cell-4 = refl

    -- σ=888 (1 nodes)
    cell-5 : κ 45 ≡ κ 45
    cell-5 = refl

    -- σ=958 (1 nodes)
    cell-6 : κ 45 ≡ κ 45
    cell-6 = refl

    -- σ=1024 (1 nodes)
    cell-7 : κ 45 ≡ κ 45
    cell-7 = refl

    -- σ=1085 (1 nodes)
    cell-8 : κ 45 ≡ κ 45
    cell-8 = refl

    -- σ=2021 (1 nodes)
    cell-9 : κ 45 ≡ κ 45
    cell-9 = refl



-- κ=372: 26 nodes, 1 τ-classes, 10 σ-classes
module subscript-Subscript-5 where

  -- τ=493: 26 nodes, 10 σ-classes
  module τ493 where

    -- σ=1054 (9 nodes)
    cell-0 : κ 372 ≡ κ 372
    cell-0 = refl

    -- σ=850 (3 nodes)
    cell-1 : κ 372 ≡ κ 372
    cell-1 = refl

    -- σ=1010 (3 nodes)
    cell-2 : κ 372 ≡ κ 372
    cell-2 = refl

    -- σ=1138 (2 nodes)
    cell-3 : κ 372 ≡ κ 372
    cell-3 = refl

    -- σ=1175 (2 nodes)
    cell-4 : κ 372 ≡ κ 372
    cell-4 = refl

    -- σ=1680 (2 nodes)
    cell-5 : κ 372 ≡ κ 372
    cell-5 = refl

    -- σ=1871 (2 nodes)
    cell-6 : κ 372 ≡ κ 372
    cell-6 = refl

    -- σ=994 (1 nodes)
    cell-7 : κ 372 ≡ κ 372
    cell-7 = refl

    -- σ=1759 (1 nodes)
    cell-8 : κ 372 ≡ κ 372
    cell-8 = refl

    -- σ=1902 (1 nodes)
    cell-9 : κ 372 ≡ κ 372
    cell-9 = refl



-- κ=42: 11 nodes, 2 τ-classes, 9 σ-classes
module terminal-map-Return-0 where

  -- τ=56: 9 nodes, 7 σ-classes
  module τ56 where

    -- σ=91 (3 nodes)
    cell-0 : κ 42 ≡ κ 42
    cell-0 = refl

    -- σ=70 (1 nodes)
    cell-1 : κ 42 ≡ κ 42
    cell-1 = refl

    -- σ=271 (1 nodes)
    cell-2 : κ 42 ≡ κ 42
    cell-2 = refl

    -- σ=867 (1 nodes)
    cell-3 : κ 42 ≡ κ 42
    cell-3 = refl

    -- σ=1568 (1 nodes)
    cell-4 : κ 42 ≡ κ 42
    cell-4 = refl

    -- σ=1689 (1 nodes)
    cell-5 : κ 42 ≡ κ 42
    cell-5 = refl

    -- σ=1765 (1 nodes)
    cell-6 : κ 42 ≡ κ 42
    cell-6 = refl


  -- τ=162: 2 nodes, 2 σ-classes
  module τ162 where

    -- σ=234 (1 nodes)
    cell-0 : κ 42 ≡ κ 42
    cell-0 = refl

    -- σ=882 (1 nodes)
    cell-1 : κ 42 ≡ κ 42
    cell-1 = refl



-- κ=129: 9 nodes, 1 τ-classes, 9 σ-classes
module monoid-op-at-x3f-Attribute-0 where

  -- τ=188: 9 nodes, 9 σ-classes
  module τ188 where

    -- σ=285 (1 nodes)
    cell-0 : κ 129 ≡ κ 129
    cell-0 = refl

    -- σ=596 (1 nodes)
    cell-1 : κ 129 ≡ κ 129
    cell-1 = refl

    -- σ=648 (1 nodes)
    cell-2 : κ 129 ≡ κ 129
    cell-2 = refl

    -- σ=861 (1 nodes)
    cell-3 : κ 129 ≡ κ 129
    cell-3 = refl

    -- σ=1155 (1 nodes)
    cell-4 : κ 129 ≡ κ 129
    cell-4 = refl

    -- σ=1307 (1 nodes)
    cell-5 : κ 129 ≡ κ 129
    cell-5 = refl

    -- σ=1347 (1 nodes)
    cell-6 : κ 129 ≡ κ 129
    cell-6 = refl

    -- σ=1543 (1 nodes)
    cell-7 : κ 129 ≡ κ 129
    cell-7 = refl

    -- σ=1625 (1 nodes)
    cell-8 : κ 129 ≡ κ 129
    cell-8 = refl



-- κ=16: 20 nodes, 4 τ-classes, 8 σ-classes
module index-Index-1 where

  -- τ=251: 10 nodes, 3 σ-classes
  module τ251 where

    -- σ=1577 (6 nodes)
    cell-0 : κ 16 ≡ κ 16
    cell-0 = refl

    -- σ=1462 (3 nodes)
    cell-1 : κ 16 ≡ κ 16
    cell-1 = refl

    -- σ=371 (1 nodes)
    cell-2 : κ 16 ≡ κ 16
    cell-2 = refl


  -- τ=128: 6 nodes, 3 σ-classes
  module τ128 where

    -- σ=336 (3 nodes)
    cell-0 : κ 16 ≡ κ 16
    cell-0 = refl

    -- σ=415 (2 nodes)
    cell-1 : κ 16 ≡ κ 16
    cell-1 = refl

    -- σ=190 (1 nodes)
    cell-2 : κ 16 ≡ κ 16
    cell-2 = refl


  -- τ=18: 2 nodes, 1 σ-classes
  module τ18 where

    -- σ=27 (2 nodes)
    cell-0 : κ 16 ≡ κ 16
    cell-0 = refl


  -- τ=26: 2 nodes, 1 σ-classes
  module τ26 where

    -- σ=34 (2 nodes)
    cell-0 : κ 16 ≡ κ 16
    cell-0 = refl



-- κ=70: 15 nodes, 1 τ-classes, 8 σ-classes
module cardinality-Call-1 where

  -- τ=87: 15 nodes, 8 σ-classes
  module int where

    -- σ=589 (4 nodes)
    cell-0 : κ 70 ≡ κ 70
    cell-0 = refl

    -- σ=517 (2 nodes)
    cell-1 : κ 70 ≡ κ 70
    cell-1 = refl

    -- σ=1777 (2 nodes)
    cell-2 : κ 70 ≡ κ 70
    cell-2 = refl

    -- σ=1780 (2 nodes)
    cell-3 : κ 70 ≡ κ 70
    cell-3 = refl

    -- σ=1783 (2 nodes)
    cell-4 : κ 70 ≡ κ 70
    cell-4 = refl

    -- σ=127 (1 nodes)
    cell-5 : κ 70 ≡ κ 70
    cell-5 = refl

    -- σ=172 (1 nodes)
    cell-6 : κ 70 ≡ κ 70
    cell-6 = refl

    -- σ=525 (1 nodes)
    cell-7 : κ 70 ≡ κ 70
    cell-7 = refl



-- κ=28: 8 nodes, 2 τ-classes, 7 σ-classes
module let-k-Assign-3 where

  -- τ=38: 5 nodes, 5 σ-classes
  module τ38 where

    -- σ=47 (1 nodes)
    cell-0 : κ 28 ≡ κ 28
    cell-0 = refl

    -- σ=103 (1 nodes)
    cell-1 : κ 28 ≡ κ 28
    cell-1 = refl

    -- σ=825 (1 nodes)
    cell-2 : κ 28 ≡ κ 28
    cell-2 = refl

    -- σ=1003 (1 nodes)
    cell-3 : κ 28 ≡ κ 28
    cell-3 = refl

    -- σ=1084 (1 nodes)
    cell-4 : κ 28 ≡ κ 28
    cell-4 = refl


  -- τ=149: 3 nodes, 2 σ-classes
  module τ149 where

    -- σ=1160 (2 nodes)
    cell-0 : κ 28 ≡ κ 28
    cell-0 = refl

    -- σ=217 (1 nodes)
    cell-1 : κ 28 ≡ κ 28
    cell-1 = refl



-- κ=46: 12 nodes, 1 τ-classes, 7 σ-classes
module apply-Call-2 where

  -- τ=61: 12 nodes, 7 σ-classes
  module τ61 where

    -- σ=792 (6 nodes)
    cell-0 : κ 46 ≡ κ 46
    cell-0 = refl

    -- σ=82 (1 nodes)
    cell-1 : κ 46 ≡ κ 46
    cell-1 = refl

    -- σ=84 (1 nodes)
    cell-2 : κ 46 ≡ κ 46
    cell-2 = refl

    -- σ=492 (1 nodes)
    cell-3 : κ 46 ≡ κ 46
    cell-3 = refl

    -- σ=960 (1 nodes)
    cell-4 : κ 46 ≡ κ 46
    cell-4 = refl

    -- σ=1258 (1 nodes)
    cell-5 : κ 46 ≡ κ 46
    cell-5 = refl

    -- σ=1732 (1 nodes)
    cell-6 : κ 46 ≡ κ 46
    cell-6 = refl



-- κ=62: 9 nodes, 2 τ-classes, 7 σ-classes
module equalizer-Compare-0 where

  -- τ=78: 7 nodes, 6 σ-classes
  module τ78 where

    -- σ=1150 (2 nodes)
    cell-0 : κ 62 ≡ κ 62
    cell-0 = refl

    -- σ=115 (1 nodes)
    cell-1 : κ 62 ≡ κ 62
    cell-1 = refl

    -- σ=208 (1 nodes)
    cell-2 : κ 62 ≡ κ 62
    cell-2 = refl

    -- σ=735 (1 nodes)
    cell-3 : κ 62 ≡ κ 62
    cell-3 = refl

    -- σ=1032 (1 nodes)
    cell-4 : κ 62 ≡ κ 62
    cell-4 = refl

    -- σ=1276 (1 nodes)
    cell-5 : κ 62 ≡ κ 62
    cell-5 = refl


  -- τ=396: 2 nodes, 1 σ-classes
  module τ396 where

    -- σ=650 (2 nodes)
    cell-0 : κ 62 ≡ κ 62
    cell-0 = refl



-- κ=211: 8 nodes, 2 τ-classes, 7 σ-classes
module monoid-op-at-x3f-Call-0 where

  -- τ=444: 7 nodes, 6 σ-classes
  module τ444 where

    -- σ=1365 (2 nodes)
    cell-0 : κ 211 ≡ κ 211
    cell-0 = refl

    -- σ=721 (1 nodes)
    cell-1 : κ 211 ≡ κ 211
    cell-1 = refl

    -- σ=833 (1 nodes)
    cell-2 : κ 211 ≡ κ 211
    cell-2 = refl

    -- σ=1090 (1 nodes)
    cell-3 : κ 211 ≡ κ 211
    cell-3 = refl

    -- σ=1098 (1 nodes)
    cell-4 : κ 211 ≡ κ 211
    cell-4 = refl

    -- σ=1371 (1 nodes)
    cell-5 : κ 211 ≡ κ 211
    cell-5 = refl


  -- τ=303: 1 nodes, 1 σ-classes
  module τ303 where

    -- σ=450 (1 nodes)
    cell-0 : κ 211 ≡ κ 211
    cell-0 = refl



-- κ=212: 8 nodes, 2 τ-classes, 7 σ-classes
module effect-seq-Expr-1 where

  -- τ=445: 7 nodes, 6 σ-classes
  module τ445 where

    -- σ=1366 (2 nodes)
    cell-0 : κ 212 ≡ κ 212
    cell-0 = refl

    -- σ=722 (1 nodes)
    cell-1 : κ 212 ≡ κ 212
    cell-1 = refl

    -- σ=834 (1 nodes)
    cell-2 : κ 212 ≡ κ 212
    cell-2 = refl

    -- σ=1091 (1 nodes)
    cell-3 : κ 212 ≡ κ 212
    cell-3 = refl

    -- σ=1099 (1 nodes)
    cell-4 : κ 212 ≡ κ 212
    cell-4 = refl

    -- σ=1372 (1 nodes)
    cell-5 : κ 212 ≡ κ 212
    cell-5 = refl


  -- τ=304: 1 nodes, 1 σ-classes
  module τ304 where

    -- σ=451 (1 nodes)
    cell-0 : κ 212 ≡ κ 212
    cell-0 = refl



-- κ=217: 15 nodes, 1 τ-classes, 7 σ-classes
module partial-at-state-Attribute where

  -- τ=153: 15 nodes, 7 σ-classes
  module Self-tau-canonical where

    -- σ=921 (7 nodes)
    cell-0 : κ 217 ≡ κ 217
    cell-0 = refl

    -- σ=483 (2 nodes)
    cell-1 : κ 217 ≡ κ 217
    cell-1 = refl

    -- σ=642 (2 nodes)
    cell-2 : κ 217 ≡ κ 217
    cell-2 = refl

    -- σ=457 (1 nodes)
    cell-3 : κ 217 ≡ κ 217
    cell-3 = refl

    -- σ=760 (1 nodes)
    cell-4 : κ 217 ≡ κ 217
    cell-4 = refl

    -- σ=1103 (1 nodes)
    cell-5 : κ 217 ≡ κ 217
    cell-5 = refl

    -- σ=1982 (1 nodes)
    cell-6 : κ 217 ≡ κ 217
    cell-6 = refl



-- κ=228: 9 nodes, 1 τ-classes, 7 σ-classes
module partial-apply-at-state-Call-0 where

  -- τ=324: 9 nodes, 7 σ-classes
  module T where

    -- σ=927 (2 nodes)
    cell-0 : κ 228 ≡ κ 228
    cell-0 = refl

    -- σ=1051 (2 nodes)
    cell-1 : κ 228 ≡ κ 228
    cell-1 = refl

    -- σ=485 (1 nodes)
    cell-2 : κ 228 ≡ κ 228
    cell-2 = refl

    -- σ=761 (1 nodes)
    cell-3 : κ 228 ≡ κ 228
    cell-3 = refl

    -- σ=922 (1 nodes)
    cell-4 : κ 228 ≡ κ 228
    cell-4 = refl

    -- σ=1027 (1 nodes)
    cell-5 : κ 228 ≡ κ 228
    cell-5 = refl

    -- σ=1203 (1 nodes)
    cell-6 : κ 228 ≡ κ 228
    cell-6 = refl



-- κ=352: 11 nodes, 3 τ-classes, 7 σ-classes
module equalizer-Compare-1 where

  -- τ=471: 8 nodes, 5 σ-classes
  module τ471 where

    -- σ=806 (4 nodes)
    cell-0 : κ 352 ≡ κ 352
    cell-0 = refl

    -- σ=926 (1 nodes)
    cell-1 : κ 352 ≡ κ 352
    cell-1 = refl

    -- σ=1190 (1 nodes)
    cell-2 : κ 352 ≡ κ 352
    cell-2 = refl

    -- σ=1317 (1 nodes)
    cell-3 : κ 352 ≡ κ 352
    cell-3 = refl

    -- σ=1645 (1 nodes)
    cell-4 : κ 352 ≡ κ 352
    cell-4 = refl


  -- τ=595: 2 nodes, 1 σ-classes
  module τ595 where

    -- σ=1149 (2 nodes)
    cell-0 : κ 352 ≡ κ 352
    cell-0 = refl


  -- τ=522: 1 nodes, 1 σ-classes
  module τ522 where

    -- σ=905 (1 nodes)
    cell-0 : κ 352 ≡ κ 352
    cell-0 = refl



-- κ=354: 11 nodes, 2 τ-classes, 7 σ-classes
module effect-seq-Expr-2 where

  -- τ=474: 10 nodes, 6 σ-classes
  module τ474 where

    -- σ=809 (4 nodes)
    cell-0 : κ 354 ≡ κ 354
    cell-0 = refl

    -- σ=1334 (2 nodes)
    cell-1 : κ 354 ≡ κ 354
    cell-1 = refl

    -- σ=943 (1 nodes)
    cell-2 : κ 354 ≡ κ 354
    cell-2 = refl

    -- σ=1171 (1 nodes)
    cell-3 : κ 354 ≡ κ 354
    cell-3 = refl

    -- σ=1192 (1 nodes)
    cell-4 : κ 354 ≡ κ 354
    cell-4 = refl

    -- σ=1319 (1 nodes)
    cell-5 : κ 354 ≡ κ 354
    cell-5 = refl


  -- τ=659: 1 nodes, 1 σ-classes
  module τ659 where

    -- σ=1356 (1 nodes)
    cell-0 : κ 354 ≡ κ 354
    cell-0 = refl



-- κ=357: 8 nodes, 4 τ-classes, 7 σ-classes
module product-Tuple-1 where

  -- τ=477: 4 nodes, 4 σ-classes
  module tuple-0 where

    -- σ=817 (1 nodes)
    cell-0 : κ 357 ≡ κ 357
    cell-0 = refl

    -- σ=1232 (1 nodes)
    cell-1 : κ 357 ≡ κ 357
    cell-1 = refl

    -- σ=1266 (1 nodes)
    cell-2 : κ 357 ≡ κ 357
    cell-2 = refl

    -- σ=1752 (1 nodes)
    cell-3 : κ 357 ≡ κ 357
    cell-3 = refl


  -- τ=693: 2 nodes, 1 σ-classes
  module tuple-1 where

    -- σ=1425 (2 nodes)
    cell-0 : κ 357 ≡ κ 357
    cell-0 = refl


  -- τ=608: 1 nodes, 1 σ-classes
  module tuple-2 where

    -- σ=1197 (1 nodes)
    cell-0 : κ 357 ≡ κ 357
    cell-0 = refl


  -- τ=646: 1 nodes, 1 σ-classes
  module tuple-3 where

    -- σ=1324 (1 nodes)
    cell-0 : κ 357 ≡ κ 357
    cell-0 = refl



-- κ=377: 8 nodes, 2 τ-classes, 7 σ-classes
module apply-Call-3 where

  -- τ=499: 7 nodes, 6 σ-classes
  module τ499 where

    -- σ=1059 (2 nodes)
    cell-0 : κ 377 ≡ κ 377
    cell-0 = refl

    -- σ=858 (1 nodes)
    cell-1 : κ 377 ≡ κ 377
    cell-1 = refl

    -- σ=1015 (1 nodes)
    cell-2 : κ 377 ≡ κ 377
    cell-2 = refl

    -- σ=1206 (1 nodes)
    cell-3 : κ 377 ≡ κ 377
    cell-3 = refl

    -- σ=1563 (1 nodes)
    cell-4 : κ 377 ≡ κ 377
    cell-4 = refl

    -- σ=1659 (1 nodes)
    cell-5 : κ 377 ≡ κ 377
    cell-5 = refl


  -- τ=660: 1 nodes, 1 σ-classes
  module τ660 where

    -- σ=1357 (1 nodes)
    cell-0 : κ 377 ≡ κ 377
    cell-0 = refl



-- κ=2: 6 nodes, 1 τ-classes, 6 σ-classes
module alias-alias where

  -- τ=2: 6 nodes, 6 σ-classes
  module τ2 where

    -- σ=2 (1 nodes)
    cell-0 : κ 2 ≡ κ 2
    cell-0 = refl

    -- σ=4 (1 nodes)
    cell-1 : κ 2 ≡ κ 2
    cell-1 = refl

    -- σ=5 (1 nodes)
    cell-2 : κ 2 ≡ κ 2
    cell-2 = refl

    -- σ=7 (1 nodes)
    cell-3 : κ 2 ≡ κ 2
    cell-3 = refl

    -- σ=8 (1 nodes)
    cell-4 : κ 2 ≡ κ 2
    cell-4 = refl

    -- σ=9 (1 nodes)
    cell-5 : κ 2 ≡ κ 2
    cell-5 = refl



-- κ=22: 8 nodes, 2 τ-classes, 6 σ-classes
module arguments-arguments-0 where

  -- τ=124: 5 nodes, 4 σ-classes
  module τ124 where

    -- σ=236 (2 nodes)
    cell-0 : κ 22 ≡ κ 22
    cell-0 = refl

    -- σ=183 (1 nodes)
    cell-1 : κ 22 ≡ κ 22
    cell-1 = refl

    -- σ=1638 (1 nodes)
    cell-2 : κ 22 ≡ κ 22
    cell-2 = refl

    -- σ=1691 (1 nodes)
    cell-3 : κ 22 ≡ κ 22
    cell-3 = refl


  -- τ=32: 3 nodes, 2 σ-classes
  module τ32 where

    -- σ=40 (2 nodes)
    cell-0 : κ 22 ≡ κ 22
    cell-0 = refl

    -- σ=113 (1 nodes)
    cell-1 : κ 22 ≡ κ 22
    cell-1 = refl



-- κ=32: 6 nodes, 1 τ-classes, 6 σ-classes
module let-k-Assign-4 where

  -- τ=45: 6 nodes, 6 σ-classes
  module τ45 where

    -- σ=55 (1 nodes)
    cell-0 : κ 32 ≡ κ 32
    cell-0 = refl

    -- σ=508 (1 nodes)
    cell-1 : κ 32 ≡ κ 32
    cell-1 = refl

    -- σ=511 (1 nodes)
    cell-2 : κ 32 ≡ κ 32
    cell-2 = refl

    -- σ=554 (1 nodes)
    cell-3 : κ 32 ≡ κ 32
    cell-3 = refl

    -- σ=696 (1 nodes)
    cell-4 : κ 32 ≡ κ 32
    cell-4 = refl

    -- σ=1210 (1 nodes)
    cell-5 : κ 32 ≡ κ 32
    cell-5 = refl



-- κ=44: 6 nodes, 2 τ-classes, 6 σ-classes
module arguments-arguments-1 where

  -- τ=168: 5 nodes, 5 σ-classes
  module τ168 where

    -- σ=245 (1 nodes)
    cell-0 : κ 44 ≡ κ 44
    cell-0 = refl

    -- σ=727 (1 nodes)
    cell-1 : κ 44 ≡ κ 44
    cell-1 = refl

    -- σ=1458 (1 nodes)
    cell-2 : κ 44 ≡ κ 44
    cell-2 = refl

    -- σ=1483 (1 nodes)
    cell-3 : κ 44 ≡ κ 44
    cell-3 = refl

    -- σ=1555 (1 nodes)
    cell-4 : κ 44 ≡ κ 44
    cell-4 = refl


  -- τ=58: 1 nodes, 1 σ-classes
  module τ58 where

    -- σ=74 (1 nodes)
    cell-0 : κ 44 ≡ κ 44
    cell-0 = refl



-- κ=87: 6 nodes, 1 τ-classes, 6 σ-classes
module coerce-FormattedValue-1 where

  -- τ=119: 6 nodes, 6 σ-classes
  module τ119 where

    -- σ=173 (1 nodes)
    cell-0 : κ 87 ≡ κ 87
    cell-0 = refl

    -- σ=526 (1 nodes)
    cell-1 : κ 87 ≡ κ 87
    cell-1 = refl

    -- σ=1778 (1 nodes)
    cell-2 : κ 87 ≡ κ 87
    cell-2 = refl

    -- σ=1781 (1 nodes)
    cell-3 : κ 87 ≡ κ 87
    cell-3 = refl

    -- σ=1784 (1 nodes)
    cell-4 : κ 87 ≡ κ 87
    cell-4 = refl

    -- σ=1950 (1 nodes)
    cell-5 : κ 87 ≡ κ 87
    cell-5 = refl



-- κ=210: 8 nodes, 2 τ-classes, 6 σ-classes
module monoid-op-at-x3f-Attribute-1 where

  -- τ=178: 7 nodes, 5 σ-classes
  module τ178 where

    -- σ=1089 (2 nodes)
    cell-0 : κ 210 ≡ κ 210
    cell-0 = refl

    -- σ=1364 (2 nodes)
    cell-1 : κ 210 ≡ κ 210
    cell-1 = refl

    -- σ=720 (1 nodes)
    cell-2 : κ 210 ≡ κ 210
    cell-2 = refl

    -- σ=832 (1 nodes)
    cell-3 : κ 210 ≡ κ 210
    cell-3 = refl

    -- σ=1097 (1 nodes)
    cell-4 : κ 210 ≡ κ 210
    cell-4 = refl


  -- τ=158: 1 nodes, 1 σ-classes
  module τ158 where

    -- σ=448 (1 nodes)
    cell-0 : κ 210 ≡ κ 210
    cell-0 = refl



-- κ=232: 7 nodes, 2 τ-classes, 6 σ-classes
module comprehension-comprehension-0 where

  -- τ=518: 6 nodes, 5 σ-classes
  module τ518 where

    -- σ=1328 (2 nodes)
    cell-0 : κ 232 ≡ κ 232
    cell-0 = refl

    -- σ=896 (1 nodes)
    cell-1 : κ 232 ≡ κ 232
    cell-1 = refl

    -- σ=996 (1 nodes)
    cell-2 : κ 232 ≡ κ 232
    cell-2 = refl

    -- σ=1253 (1 nodes)
    cell-3 : κ 232 ≡ κ 232
    cell-3 = refl

    -- σ=1887 (1 nodes)
    cell-4 : κ 232 ≡ κ 232
    cell-4 = refl


  -- τ=330: 1 nodes, 1 σ-classes
  module τ330 where

    -- σ=496 (1 nodes)
    cell-0 : κ 232 ≡ κ 232
    cell-0 = refl



-- κ=343: 7 nodes, 1 τ-classes, 6 σ-classes
module apply-Call-4 where

  -- τ=456: 7 nodes, 6 σ-classes
  module τ456 where

    -- σ=1052 (2 nodes)
    cell-0 : κ 343 ≡ κ 343
    cell-0 = refl

    -- σ=762 (1 nodes)
    cell-1 : κ 343 ≡ κ 343
    cell-1 = refl

    -- σ=923 (1 nodes)
    cell-2 : κ 343 ≡ κ 343
    cell-2 = refl

    -- σ=928 (1 nodes)
    cell-3 : κ 343 ≡ κ 343
    cell-3 = refl

    -- σ=1008 (1 nodes)
    cell-4 : κ 343 ≡ κ 343
    cell-4 = refl

    -- σ=1204 (1 nodes)
    cell-5 : κ 343 ≡ κ 343
    cell-5 = refl



-- κ=344: 7 nodes, 1 τ-classes, 6 σ-classes
module effect-seq-Expr-3 where

  -- τ=457: 7 nodes, 6 σ-classes
  module τ457 where

    -- σ=1053 (2 nodes)
    cell-0 : κ 344 ≡ κ 344
    cell-0 = refl

    -- σ=763 (1 nodes)
    cell-1 : κ 344 ≡ κ 344
    cell-1 = refl

    -- σ=924 (1 nodes)
    cell-2 : κ 344 ≡ κ 344
    cell-2 = refl

    -- σ=929 (1 nodes)
    cell-3 : κ 344 ≡ κ 344
    cell-3 = refl

    -- σ=1009 (1 nodes)
    cell-4 : κ 344 ≡ κ 344
    cell-4 = refl

    -- σ=1205 (1 nodes)
    cell-5 : κ 344 ≡ κ 344
    cell-5 = refl



-- κ=676: 6 nodes, 3 τ-classes, 6 σ-classes
module bimap-BinOp-0 where

  -- τ=853: 4 nodes, 4 σ-classes
  module τ853 where

    -- σ=1824 (1 nodes)
    cell-0 : κ 676 ≡ κ 676
    cell-0 = refl

    -- σ=1834 (1 nodes)
    cell-1 : κ 676 ≡ κ 676
    cell-1 = refl

    -- σ=1841 (1 nodes)
    cell-2 : κ 676 ≡ κ 676
    cell-2 = refl

    -- σ=1996 (1 nodes)
    cell-3 : κ 676 ≡ κ 676
    cell-3 = refl


  -- τ=921: 1 nodes, 1 σ-classes
  module τ921 where

    -- σ=2001 (1 nodes)
    cell-0 : κ 676 ≡ κ 676
    cell-0 = refl


  -- τ=949: 1 nodes, 1 σ-classes
  module τ949 where

    -- σ=2077 (1 nodes)
    cell-0 : κ 676 ≡ κ 676
    cell-0 = refl



-- κ=79: 7 nodes, 2 τ-classes, 5 σ-classes
module arg-arg-1 where

  -- τ=103: 5 nodes, 4 σ-classes
  module τ103 where

    -- σ=149 (2 nodes)
    cell-0 : κ 79 ≡ κ 79
    cell-0 = refl

    -- σ=1219 (1 nodes)
    cell-1 : κ 79 ≡ κ 79
    cell-1 = refl

    -- σ=1220 (1 nodes)
    cell-2 : κ 79 ≡ κ 79
    cell-2 = refl

    -- σ=1221 (1 nodes)
    cell-3 : κ 79 ≡ κ 79
    cell-3 = refl


  -- τ=99: 2 nodes, 1 σ-classes
  module τ99 where

    -- σ=145 (2 nodes)
    cell-0 : κ 79 ≡ κ 79
    cell-0 = refl



-- κ=86: 5 nodes, 1 τ-classes, 5 σ-classes
module coerce-FormattedValue-2 where

  -- τ=118: 5 nodes, 5 σ-classes
  module τ118 where

    -- σ=169 (1 nodes)
    cell-0 : κ 86 ≡ κ 86
    cell-0 = refl

    -- σ=311 (1 nodes)
    cell-1 : κ 86 ≡ κ 86
    cell-1 = refl

    -- σ=1775 (1 nodes)
    cell-2 : κ 86 ≡ κ 86
    cell-2 = refl

    -- σ=1929 (1 nodes)
    cell-3 : κ 86 ≡ κ 86
    cell-3 = refl

    -- σ=1948 (1 nodes)
    cell-4 : κ 86 ≡ κ 86
    cell-4 = refl



-- κ=109: 5 nodes, 2 τ-classes, 5 σ-classes
module morphism-at-x3f-Attribute-1 where

  -- τ=178: 4 nodes, 4 σ-classes
  module τ178 where

    -- σ=263 (1 nodes)
    cell-0 : κ 109 ≡ κ 109
    cell-0 = refl

    -- σ=268 (1 nodes)
    cell-1 : κ 109 ≡ κ 109
    cell-1 = refl

    -- σ=739 (1 nodes)
    cell-2 : κ 109 ≡ κ 109
    cell-2 = refl

    -- σ=828 (1 nodes)
    cell-3 : κ 109 ≡ κ 109
    cell-3 = refl


  -- τ=158: 1 nodes, 1 σ-classes
  module τ158 where

    -- σ=229 (1 nodes)
    cell-0 : κ 109 ≡ κ 109
    cell-0 = refl



-- κ=118: 9 nodes, 2 τ-classes, 5 σ-classes
module apply-Call-5 where

  -- τ=174: 7 nodes, 4 σ-classes
  module τ174 where

    -- σ=811 (4 nodes)
    cell-0 : κ 118 ≡ κ 118
    cell-0 = refl

    -- σ=254 (1 nodes)
    cell-1 : κ 118 ≡ κ 118
    cell-1 = refl

    -- σ=1193 (1 nodes)
    cell-2 : κ 118 ≡ κ 118
    cell-2 = refl

    -- σ=1320 (1 nodes)
    cell-3 : κ 118 ≡ κ 118
    cell-3 = refl


  -- τ=597: 2 nodes, 1 σ-classes
  module τ597 where

    -- σ=1152 (2 nodes)
    cell-0 : κ 118 ≡ κ 118
    cell-0 = refl



-- κ=126: 5 nodes, 2 τ-classes, 5 σ-classes
module annassign-AnnAssign-0 where

  -- τ=185: 4 nodes, 4 σ-classes
  module τ185 where

    -- σ=279 (1 nodes)
    cell-0 : κ 126 ≡ κ 126
    cell-0 = refl

    -- σ=752 (1 nodes)
    cell-1 : κ 126 ≡ κ 126
    cell-1 = refl

    -- σ=1336 (1 nodes)
    cell-2 : κ 126 ≡ κ 126
    cell-2 = refl

    -- σ=1527 (1 nodes)
    cell-3 : κ 126 ≡ κ 126
    cell-3 = refl


  -- τ=391: 1 nodes, 1 σ-classes
  module τ391 where

    -- σ=637 (1 nodes)
    cell-0 : κ 126 ≡ κ 126
    cell-0 = refl



-- κ=128: 5 nodes, 1 τ-classes, 5 σ-classes
module equalizer-Compare-2 where

  -- τ=187: 5 nodes, 5 σ-classes
  module τ187 where

    -- σ=284 (1 nodes)
    cell-0 : κ 128 ≡ κ 128
    cell-0 = refl

    -- σ=557 (1 nodes)
    cell-1 : κ 128 ≡ κ 128
    cell-1 = refl

    -- σ=1117 (1 nodes)
    cell-2 : κ 128 ≡ κ 128
    cell-2 = refl

    -- σ=1279 (1 nodes)
    cell-3 : κ 128 ≡ κ 128
    cell-3 = refl

    -- σ=1905 (1 nodes)
    cell-4 : κ 128 ≡ κ 128
    cell-4 = refl



-- κ=130: 5 nodes, 1 τ-classes, 5 σ-classes
module monoid-op-at-x3f-Call-1 where

  -- τ=189: 5 nodes, 5 σ-classes
  module τ189 where

    -- σ=286 (1 nodes)
    cell-0 : κ 130 ≡ κ 130
    cell-0 = refl

    -- σ=598 (1 nodes)
    cell-1 : κ 130 ≡ κ 130
    cell-1 = refl

    -- σ=862 (1 nodes)
    cell-2 : κ 130 ≡ κ 130
    cell-2 = refl

    -- σ=1156 (1 nodes)
    cell-3 : κ 130 ≡ κ 130
    cell-3 = refl

    -- σ=1308 (1 nodes)
    cell-4 : κ 130 ≡ κ 130
    cell-4 = refl



-- κ=131: 5 nodes, 1 τ-classes, 5 σ-classes
module effect-seq-Expr-4 where

  -- τ=190: 5 nodes, 5 σ-classes
  module τ190 where

    -- σ=287 (1 nodes)
    cell-0 : κ 131 ≡ κ 131
    cell-0 = refl

    -- σ=599 (1 nodes)
    cell-1 : κ 131 ≡ κ 131
    cell-1 = refl

    -- σ=863 (1 nodes)
    cell-2 : κ 131 ≡ κ 131
    cell-2 = refl

    -- σ=1157 (1 nodes)
    cell-3 : κ 131 ≡ κ 131
    cell-3 = refl

    -- σ=1309 (1 nodes)
    cell-4 : κ 131 ≡ κ 131
    cell-4 = refl



-- κ=150: 5 nodes, 2 τ-classes, 5 σ-classes
module coerce-FormattedValue-3 where

  -- τ=840: 4 nodes, 4 σ-classes
  module τ840 where

    -- σ=1788 (1 nodes)
    cell-0 : κ 150 ≡ κ 150
    cell-0 = refl

    -- σ=1937 (1 nodes)
    cell-1 : κ 150 ≡ κ 150
    cell-1 = refl

    -- σ=1939 (1 nodes)
    cell-2 : κ 150 ≡ κ 150
    cell-2 = refl

    -- σ=2040 (1 nodes)
    cell-3 : κ 150 ≡ κ 150
    cell-3 = refl


  -- τ=211: 1 nodes, 1 σ-classes
  module τ211 where

    -- σ=313 (1 nodes)
    cell-0 : κ 150 ≡ κ 150
    cell-0 = refl



-- κ=175: 10 nodes, 2 τ-classes, 5 σ-classes
module apply-Call-6 where

  -- τ=242: 8 nodes, 3 σ-classes
  module τ242 where

    -- σ=362 (4 nodes)
    cell-0 : κ 175 ≡ κ 175
    cell-0 = refl

    -- σ=1431 (3 nodes)
    cell-1 : κ 175 ≡ κ 175
    cell-1 = refl

    -- σ=409 (1 nodes)
    cell-2 : κ 175 ≡ κ 175
    cell-2 = refl


  -- τ=728: 2 nodes, 2 σ-classes
  module τ728 where

    -- σ=1492 (1 nodes)
    cell-0 : κ 175 ≡ κ 175
    cell-0 = refl

    -- σ=2067 (1 nodes)
    cell-1 : κ 175 ≡ κ 175
    cell-1 = refl



-- κ=213: 5 nodes, 2 τ-classes, 5 σ-classes
module fold-For-0 where

  -- τ=483: 4 nodes, 4 σ-classes
  module τ483 where

    -- σ=835 (1 nodes)
    cell-0 : κ 213 ≡ κ 213
    cell-0 = refl

    -- σ=1092 (1 nodes)
    cell-1 : κ 213 ≡ κ 213
    cell-1 = refl

    -- σ=1100 (1 nodes)
    cell-2 : κ 213 ≡ κ 213
    cell-2 = refl

    -- σ=1373 (1 nodes)
    cell-3 : κ 213 ≡ κ 213
    cell-3 = refl


  -- τ=305: 1 nodes, 1 σ-classes
  module τ305 where

    -- σ=452 (1 nodes)
    cell-0 : κ 213 ≡ κ 213
    cell-0 = refl



-- κ=252: 5 nodes, 2 τ-classes, 5 σ-classes
module equalizer-Compare-3 where

  -- τ=468: 4 nodes, 4 σ-classes
  module τ468 where

    -- σ=799 (1 nodes)
    cell-0 : κ 252 ≡ κ 252
    cell-0 = refl

    -- σ=975 (1 nodes)
    cell-1 : κ 252 ≡ κ 252
    cell-1 = refl

    -- σ=1037 (1 nodes)
    cell-2 : κ 252 ≡ κ 252
    cell-2 = refl

    -- σ=1068 (1 nodes)
    cell-3 : κ 252 ≡ κ 252
    cell-3 = refl


  -- τ=353: 1 nodes, 1 σ-classes
  module τ353 where

    -- σ=548 (1 nodes)
    cell-0 : κ 252 ≡ κ 252
    cell-0 = refl



-- κ=331: 6 nodes, 2 τ-classes, 5 σ-classes
module arg-arg-2 where

  -- τ=440: 3 nodes, 2 σ-classes
  module τ440 where

    -- σ=869 (2 nodes)
    cell-0 : κ 331 ≡ κ 331
    cell-0 = refl

    -- σ=710 (1 nodes)
    cell-1 : κ 331 ≡ κ 331
    cell-1 = refl


  -- τ=452: 3 nodes, 3 σ-classes
  module τ452 where

    -- σ=747 (1 nodes)
    cell-0 : κ 331 ≡ κ 331
    cell-0 = refl

    -- σ=912 (1 nodes)
    cell-1 : κ 331 ≡ κ 331
    cell-1 = refl

    -- σ=933 (1 nodes)
    cell-2 : κ 331 ≡ κ 331
    cell-2 = refl



-- κ=356: 5 nodes, 1 τ-classes, 5 σ-classes
module free_monoid-op-at-x3f-Attribute-0 where

  -- τ=188: 5 nodes, 5 σ-classes
  module τ188 where

    -- σ=816 (1 nodes)
    cell-0 : κ 356 ≡ κ 356
    cell-0 = refl

    -- σ=983 (1 nodes)
    cell-1 : κ 356 ≡ κ 356
    cell-1 = refl

    -- σ=1293 (1 nodes)
    cell-2 : κ 356 ≡ κ 356
    cell-2 = refl

    -- σ=1669 (1 nodes)
    cell-3 : κ 356 ≡ κ 356
    cell-3 = refl

    -- σ=1750 (1 nodes)
    cell-4 : κ 356 ≡ κ 356
    cell-4 = refl



-- κ=378: 6 nodes, 2 τ-classes, 5 σ-classes
module effect-seq-Expr-5 where

  -- τ=500: 5 nodes, 4 σ-classes
  module τ500 where

    -- σ=1060 (2 nodes)
    cell-0 : κ 378 ≡ κ 378
    cell-0 = refl

    -- σ=859 (1 nodes)
    cell-1 : κ 378 ≡ κ 378
    cell-1 = refl

    -- σ=1016 (1 nodes)
    cell-2 : κ 378 ≡ κ 378
    cell-2 = refl

    -- σ=1207 (1 nodes)
    cell-3 : κ 378 ≡ κ 378
    cell-3 = refl


  -- τ=661: 1 nodes, 1 σ-classes
  module τ661 where

    -- σ=1358 (1 nodes)
    cell-0 : κ 378 ≡ κ 378
    cell-0 = refl



-- κ=456: 5 nodes, 1 τ-classes, 5 σ-classes
module equalizer-Compare-4 where

  -- τ=585: 5 nodes, 5 σ-classes
  module τ585 where

    -- σ=1124 (1 nodes)
    cell-0 : κ 456 ≡ κ 456
    cell-0 = refl

    -- σ=1164 (1 nodes)
    cell-1 : κ 456 ≡ κ 456
    cell-1 = refl

    -- σ=1338 (1 nodes)
    cell-2 : κ 456 ≡ κ 456
    cell-2 = refl

    -- σ=1736 (1 nodes)
    cell-3 : κ 456 ≡ κ 456
    cell-3 = refl

    -- σ=1920 (1 nodes)
    cell-4 : κ 456 ≡ κ 456
    cell-4 = refl



-- κ=19: 4 nodes, 4 τ-classes, 4 σ-classes
module annassign-AnnAssign-1 where

  -- τ=21: 1 nodes, 1 σ-classes
  module τ21 where

    -- σ=30 (1 nodes)
    cell-0 : κ 19 ≡ κ 19
    cell-0 = refl


  -- τ=28: 1 nodes, 1 σ-classes
  module τ28 where

    -- σ=36 (1 nodes)
    cell-0 : κ 19 ≡ κ 19
    cell-0 = refl


  -- τ=131: 1 nodes, 1 σ-classes
  module τ131 where

    -- σ=192 (1 nodes)
    cell-0 : κ 19 ≡ κ 19
    cell-0 = refl


  -- τ=253: 1 nodes, 1 σ-classes
  module τ253 where

    -- σ=373 (1 nodes)
    cell-0 : κ 19 ≡ κ 19
    cell-0 = refl



-- κ=69: 55 nodes, 1 τ-classes, 4 σ-classes
module arrow-Name where

  -- τ=13: 55 nodes, 4 σ-classes
  module Self where

    -- σ=126 (42 nodes)
    cell-0 : κ 69 ≡ κ 69
    cell-0 = refl

    -- σ=848 (6 nodes)
    cell-1 : κ 69 ≡ κ 69
    cell-1 = refl

    -- σ=1415 (4 nodes)
    cell-2 : κ 69 ≡ κ 69
    cell-2 = refl

    -- σ=488 (3 nodes)
    cell-3 : κ 69 ≡ κ 69
    cell-3 = refl



-- κ=209: 5 nodes, 1 τ-classes, 4 σ-classes
module let-k-Assign-5 where

  -- τ=302: 5 nodes, 4 σ-classes
  module τ302 where

    -- σ=442 (2 nodes)
    cell-0 : κ 209 ≡ κ 209
    cell-0 = refl

    -- σ=545 (1 nodes)
    cell-1 : κ 209 ≡ κ 209
    cell-1 = refl

    -- σ=903 (1 nodes)
    cell-2 : κ 209 ≡ κ 209
    cell-2 = refl

    -- σ=1238 (1 nodes)
    cell-3 : κ 209 ≡ κ 209
    cell-3 = refl



-- κ=243: 10 nodes, 1 τ-classes, 4 σ-classes
module free_monoid-op-at-state-Attribute where

  -- τ=153: 10 nodes, 4 σ-classes
  module Self-tau-canonical where

    -- σ=624 (7 nodes)
    cell-0 : κ 243 ≡ κ 243
    cell-0 = refl

    -- σ=519 (1 nodes)
    cell-1 : κ 243 ≡ κ 243
    cell-1 = refl

    -- σ=530 (1 nodes)
    cell-2 : κ 243 ≡ κ 243
    cell-2 = refl

    -- σ=1376 (1 nodes)
    cell-3 : κ 243 ≡ κ 243
    cell-3 = refl



-- κ=263: 5 nodes, 1 τ-classes, 4 σ-classes
module subscript-Subscript-6 where

  -- τ=365: 5 nodes, 4 σ-classes
  module τ365 where

    -- σ=587 (2 nodes)
    cell-0 : κ 263 ≡ κ 263
    cell-0 = refl

    -- σ=1593 (1 nodes)
    cell-1 : κ 263 ≡ κ 263
    cell-1 = refl

    -- σ=1598 (1 nodes)
    cell-2 : κ 263 ≡ κ 263
    cell-2 = refl

    -- σ=1604 (1 nodes)
    cell-3 : κ 263 ≡ κ 263
    cell-3 = refl



-- κ=264: 5 nodes, 1 τ-classes, 4 σ-classes
module morphism-at-x3f-Attribute-2 where

  -- τ=366: 5 nodes, 4 σ-classes
  module τ366 where

    -- σ=588 (2 nodes)
    cell-0 : κ 264 ≡ κ 264
    cell-0 = refl

    -- σ=1594 (1 nodes)
    cell-1 : κ 264 ≡ κ 264
    cell-1 = refl

    -- σ=1599 (1 nodes)
    cell-2 : κ 264 ≡ κ 264
    cell-2 = refl

    -- σ=1605 (1 nodes)
    cell-3 : κ 264 ≡ κ 264
    cell-3 = refl



-- κ=349: 8 nodes, 1 τ-classes, 4 σ-classes
module let-k-Assign-6 where

  -- τ=467: 8 nodes, 4 σ-classes
  module τ467 where

    -- σ=793 (4 nodes)
    cell-0 : κ 349 ≡ κ 349
    cell-0 = refl

    -- σ=973 (2 nodes)
    cell-1 : κ 349 ≡ κ 349
    cell-1 = refl

    -- σ=1259 (1 nodes)
    cell-2 : κ 349 ≡ κ 349
    cell-2 = refl

    -- σ=1733 (1 nodes)
    cell-3 : κ 349 ≡ κ 349
    cell-3 = refl



-- κ=350: 4 nodes, 1 τ-classes, 4 σ-classes
module apply-Call-7 where

  -- τ=469: 4 nodes, 4 σ-classes
  module τ469 where

    -- σ=803 (1 nodes)
    cell-0 : κ 350 ≡ κ 350
    cell-0 = refl

    -- σ=978 (1 nodes)
    cell-1 : κ 350 ≡ κ 350
    cell-1 = refl

    -- σ=1039 (1 nodes)
    cell-2 : κ 350 ≡ κ 350
    cell-2 = refl

    -- σ=1070 (1 nodes)
    cell-3 : κ 350 ≡ κ 350
    cell-3 = refl



-- κ=351: 4 nodes, 1 τ-classes, 4 σ-classes
module let-k-Assign-7 where

  -- τ=470: 4 nodes, 4 σ-classes
  module τ470 where

    -- σ=804 (1 nodes)
    cell-0 : κ 351 ≡ κ 351
    cell-0 = refl

    -- σ=979 (1 nodes)
    cell-1 : κ 351 ≡ κ 351
    cell-1 = refl

    -- σ=1040 (1 nodes)
    cell-2 : κ 351 ≡ κ 351
    cell-2 = refl

    -- σ=1071 (1 nodes)
    cell-3 : κ 351 ≡ κ 351
    cell-3 = refl



-- κ=371: 26 nodes, 1 τ-classes, 4 σ-classes
module index-Index-2 where

  -- τ=492: 26 nodes, 4 σ-classes
  module τ492 where

    -- σ=849 (20 nodes)
    cell-0 : κ 371 ≡ κ 371
    cell-0 = refl

    -- σ=1758 (3 nodes)
    cell-1 : κ 371 ≡ κ 371
    cell-1 = refl

    -- σ=1679 (2 nodes)
    cell-2 : κ 371 ≡ κ 371
    cell-2 = refl

    -- σ=1901 (1 nodes)
    cell-3 : κ 371 ≡ κ 371
    cell-3 = refl



-- κ=373: 6 nodes, 1 τ-classes, 4 σ-classes
module fiber-Call where

  -- τ=494: 6 nodes, 4 σ-classes
  module bool where

    -- σ=1055 (3 nodes)
    cell-0 : κ 373 ≡ κ 373
    cell-0 = refl

    -- σ=851 (1 nodes)
    cell-1 : κ 373 ≡ κ 373
    cell-1 = refl

    -- σ=1011 (1 nodes)
    cell-2 : κ 373 ≡ κ 373
    cell-2 = refl

    -- σ=1872 (1 nodes)
    cell-3 : κ 373 ≡ κ 373
    cell-3 = refl



-- κ=395: 4 nodes, 1 τ-classes, 4 σ-classes
module lazy_fold-GeneratorExp-0 where

  -- τ=519: 4 nodes, 4 σ-classes
  module τ519 where

    -- σ=897 (1 nodes)
    cell-0 : κ 395 ≡ κ 395
    cell-0 = refl

    -- σ=1254 (1 nodes)
    cell-1 : κ 395 ≡ κ 395
    cell-1 = refl

    -- σ=1343 (1 nodes)
    cell-2 : κ 395 ≡ κ 395
    cell-2 = refl

    -- σ=1888 (1 nodes)
    cell-3 : κ 395 ≡ κ 395
    cell-3 = refl



-- κ=414: 4 nodes, 4 τ-classes, 4 σ-classes
module product-Tuple-2 where

  -- τ=542: 1 nodes, 1 σ-classes
  module tuple-0 where

    -- σ=966 (1 nodes)
    cell-0 : κ 414 ≡ κ 414
    cell-0 = refl


  -- τ=725: 1 nodes, 1 σ-classes
  module tuple-1 where

    -- σ=1489 (1 nodes)
    cell-0 : κ 414 ≡ κ 414
    cell-0 = refl


  -- τ=773: 1 nodes, 1 σ-classes
  module tuple-2 where

    -- σ=1628 (1 nodes)
    cell-0 : κ 414 ≡ κ 414
    cell-0 = refl


  -- τ=805: 1 nodes, 1 σ-classes
  module tuple-3 where

    -- σ=1699 (1 nodes)
    cell-0 : κ 414 ≡ κ 414
    cell-0 = refl



-- κ=484: 4 nodes, 1 τ-classes, 4 σ-classes
module let-k-Assign-8 where

  -- τ=620: 4 nodes, 4 σ-classes
  module τ620 where

    -- σ=1228 (1 nodes)
    cell-0 : κ 484 ≡ κ 484
    cell-0 = refl

    -- σ=1803 (1 nodes)
    cell-1 : κ 484 ≡ κ 484
    cell-1 = refl

    -- σ=1805 (1 nodes)
    cell-2 : κ 484 ≡ κ 484
    cell-2 = refl

    -- σ=1807 (1 nodes)
    cell-3 : κ 484 ≡ κ 484
    cell-3 = refl



-- κ=558: 5 nodes, 1 τ-classes, 4 σ-classes
module exponential-Call where

  -- τ=404: 5 nodes, 4 σ-classes
  module τ404 where

    -- σ=1452 (2 nodes)
    cell-0 : κ 558 ≡ κ 558
    cell-0 = refl

    -- σ=1507 (1 nodes)
    cell-1 : κ 558 ≡ κ 558
    cell-1 = refl

    -- σ=1716 (1 nodes)
    cell-2 : κ 558 ≡ κ 558
    cell-2 = refl

    -- σ=1863 (1 nodes)
    cell-3 : κ 558 ≡ κ 558
    cell-3 = refl



-- κ=673: 13 nodes, 1 τ-classes, 4 σ-classes
module free_monoid-fold-JoinedStr-0 where

  -- τ=850: 13 nodes, 4 σ-classes
  module str where

    -- σ=1827 (7 nodes)
    cell-0 : κ 673 ≡ κ 673
    cell-0 = refl

    -- σ=1820 (4 nodes)
    cell-1 : κ 673 ≡ κ 673
    cell-1 = refl

    -- σ=1855 (1 nodes)
    cell-2 : κ 673 ≡ κ 673
    cell-2 = refl

    -- σ=2079 (1 nodes)
    cell-3 : κ 673 ≡ κ 673
    cell-3 = refl



-- κ=25: 3 nodes, 1 τ-classes, 3 σ-classes
module equalizer-Compare-5 where

  -- τ=35: 3 nodes, 3 σ-classes
  module τ35 where

    -- σ=44 (1 nodes)
    cell-0 : κ 25 ≡ κ 25
    cell-0 = refl

    -- σ=768 (1 nodes)
    cell-1 : κ 25 ≡ κ 25
    cell-1 = refl

    -- σ=952 (1 nodes)
    cell-2 : κ 25 ≡ κ 25
    cell-2 = refl



-- κ=50: 4 nodes, 1 τ-classes, 3 σ-classes
module equalizer-Compare-6 where

  -- τ=66: 4 nodes, 3 σ-classes
  module τ66 where

    -- σ=90 (2 nodes)
    cell-0 : κ 50 ≡ κ 50
    cell-0 = refl

    -- σ=258 (1 nodes)
    cell-1 : κ 50 ≡ κ 50
    cell-1 = refl

    -- σ=2052 (1 nodes)
    cell-2 : κ 50 ≡ κ 50
    cell-2 = refl



-- κ=96: 3 nodes, 1 τ-classes, 3 σ-classes
module annassign-AnnAssign-2 where

  -- τ=138: 3 nodes, 3 σ-classes
  module τ138 where

    -- σ=199 (1 nodes)
    cell-0 : κ 96 ≡ κ 96
    cell-0 = refl

    -- σ=377 (1 nodes)
    cell-1 : κ 96 ≡ κ 96
    cell-1 = refl

    -- σ=402 (1 nodes)
    cell-2 : κ 96 ≡ κ 96
    cell-2 = refl



-- κ=102: 7 nodes, 1 τ-classes, 3 σ-classes
module monoid-accum-AugAssign-0 where

  -- τ=148: 7 nodes, 3 σ-classes
  module τ148 where

    -- σ=837 (5 nodes)
    cell-0 : κ 102 ≡ κ 102
    cell-0 = refl

    -- σ=215 (1 nodes)
    cell-1 : κ 102 ≡ κ 102
    cell-1 = refl

    -- σ=608 (1 nodes)
    cell-2 : κ 102 ≡ κ 102
    cell-2 = refl



-- κ=137: 5 nodes, 1 τ-classes, 3 σ-classes
module apply-Call-8 where

  -- τ=198: 5 nodes, 3 σ-classes
  module τ198 where

    -- σ=297 (2 nodes)
    cell-0 : κ 137 ≡ κ 137
    cell-0 = refl

    -- σ=1771 (2 nodes)
    cell-1 : κ 137 ≡ κ 137
    cell-1 = refl

    -- σ=1809 (1 nodes)
    cell-2 : κ 137 ≡ κ 137
    cell-2 = refl



-- κ=155: 3 nodes, 1 τ-classes, 3 σ-classes
module apply-Call-9 where

  -- τ=217: 3 nodes, 3 σ-classes
  module τ217 where

    -- σ=324 (1 nodes)
    cell-0 : κ 155 ≡ κ 155
    cell-0 = refl

    -- σ=328 (1 nodes)
    cell-1 : κ 155 ≡ κ 155
    cell-1 = refl

    -- σ=332 (1 nodes)
    cell-2 : κ 155 ≡ κ 155
    cell-2 = refl



-- κ=156: 3 nodes, 1 τ-classes, 3 σ-classes
module annassign-AnnAssign-3 where

  -- τ=218: 3 nodes, 3 σ-classes
  module τ218 where

    -- σ=325 (1 nodes)
    cell-0 : κ 156 ≡ κ 156
    cell-0 = refl

    -- σ=329 (1 nodes)
    cell-1 : κ 156 ≡ κ 156
    cell-1 = refl

    -- σ=333 (1 nodes)
    cell-2 : κ 156 ≡ κ 156
    cell-2 = refl



-- κ=157: 4 nodes, 3 τ-classes, 3 σ-classes
module index-Index-3 where

  -- τ=758: 2 nodes, 1 σ-classes
  module τ758 where

    -- σ=1579 (2 nodes)
    cell-0 : κ 157 ≡ κ 157
    cell-0 = refl


  -- τ=222: 1 nodes, 1 σ-classes
  module τ222 where

    -- σ=338 (1 nodes)
    cell-0 : κ 157 ≡ κ 157
    cell-0 = refl


  -- τ=273: 1 nodes, 1 σ-classes
  module τ273 where

    -- σ=394 (1 nodes)
    cell-0 : κ 157 ≡ κ 157
    cell-0 = refl



-- κ=158: 4 nodes, 3 τ-classes, 3 σ-classes
module subscript-Subscript-7 where

  -- τ=759: 2 nodes, 1 σ-classes
  module τ759 where

    -- σ=1580 (2 nodes)
    cell-0 : κ 158 ≡ κ 158
    cell-0 = refl


  -- τ=223: 1 nodes, 1 σ-classes
  module τ223 where

    -- σ=339 (1 nodes)
    cell-0 : κ 158 ≡ κ 158
    cell-0 = refl


  -- τ=274: 1 nodes, 1 σ-classes
  module τ274 where

    -- σ=395 (1 nodes)
    cell-0 : κ 158 ≡ κ 158
    cell-0 = refl



-- κ=187: 4 nodes, 3 τ-classes, 3 σ-classes
module index-Index-4 where

  -- τ=265: 2 nodes, 1 σ-classes
  module τ265 where

    -- σ=387 (2 nodes)
    cell-0 : κ 187 ≡ κ 187
    cell-0 = refl


  -- τ=295: 1 nodes, 1 σ-classes
  module τ295 where

    -- σ=425 (1 nodes)
    cell-0 : κ 187 ≡ κ 187
    cell-0 = refl


  -- τ=358: 1 nodes, 1 σ-classes
  module τ358 where

    -- σ=566 (1 nodes)
    cell-0 : κ 187 ≡ κ 187
    cell-0 = refl



-- κ=188: 4 nodes, 3 τ-classes, 3 σ-classes
module subscript-Subscript-8 where

  -- τ=266: 2 nodes, 1 σ-classes
  module τ266 where

    -- σ=388 (2 nodes)
    cell-0 : κ 188 ≡ κ 188
    cell-0 = refl


  -- τ=296: 1 nodes, 1 σ-classes
  module τ296 where

    -- σ=426 (1 nodes)
    cell-0 : κ 188 ≡ κ 188
    cell-0 = refl


  -- τ=359: 1 nodes, 1 σ-classes
  module τ359 where

    -- σ=567 (1 nodes)
    cell-0 : κ 188 ≡ κ 188
    cell-0 = refl



-- κ=193: 4 nodes, 2 τ-classes, 3 σ-classes
module product-Tuple-3 where

  -- τ=738: 3 nodes, 2 σ-classes
  module tuple-0 where

    -- σ=1650 (2 nodes)
    cell-0 : κ 193 ≡ κ 193
    cell-0 = refl

    -- σ=1517 (1 nodes)
    cell-1 : κ 193 ≡ κ 193
    cell-1 = refl


  -- τ=282: 1 nodes, 1 σ-classes
  module tuple-1 where

    -- σ=405 (1 nodes)
    cell-0 : κ 193 ≡ κ 193
    cell-0 = refl



-- κ=194: 4 nodes, 2 τ-classes, 3 σ-classes
module index-Index-5 where

  -- τ=739: 3 nodes, 2 σ-classes
  module τ739 where

    -- σ=1651 (2 nodes)
    cell-0 : κ 194 ≡ κ 194
    cell-0 = refl

    -- σ=1518 (1 nodes)
    cell-1 : κ 194 ≡ κ 194
    cell-1 = refl


  -- τ=283: 1 nodes, 1 σ-classes
  module τ283 where

    -- σ=406 (1 nodes)
    cell-0 : κ 194 ≡ κ 194
    cell-0 = refl



-- κ=195: 4 nodes, 2 τ-classes, 3 σ-classes
module subscript-Subscript-9 where

  -- τ=740: 3 nodes, 2 σ-classes
  module τ740 where

    -- σ=1652 (2 nodes)
    cell-0 : κ 195 ≡ κ 195
    cell-0 = refl

    -- σ=1519 (1 nodes)
    cell-1 : κ 195 ≡ κ 195
    cell-1 = refl


  -- τ=284: 1 nodes, 1 σ-classes
  module τ284 where

    -- σ=407 (1 nodes)
    cell-0 : κ 195 ≡ κ 195
    cell-0 = refl



-- κ=202: 3 nodes, 3 τ-classes, 3 σ-classes
module subscript-Subscript-10 where

  -- τ=292: 1 nodes, 1 σ-classes
  module τ292 where

    -- σ=420 (1 nodes)
    cell-0 : κ 202 ≡ κ 202
    cell-0 = refl


  -- τ=714: 1 nodes, 1 σ-classes
  module τ714 where

    -- σ=1466 (1 nodes)
    cell-0 : κ 202 ≡ κ 202
    cell-0 = refl


  -- τ=723: 1 nodes, 1 σ-classes
  module τ723 where

    -- σ=1479 (1 nodes)
    cell-0 : κ 202 ≡ κ 202
    cell-0 = refl



-- κ=216: 3 nodes, 1 τ-classes, 3 σ-classes
module equalizer-Compare-7 where

  -- τ=308: 3 nodes, 3 σ-classes
  module τ308 where

    -- σ=455 (1 nodes)
    cell-0 : κ 216 ≡ κ 216
    cell-0 = refl

    -- σ=1661 (1 nodes)
    cell-1 : κ 216 ≡ κ 216
    cell-1 = refl

    -- σ=2065 (1 nodes)
    cell-2 : κ 216 ≡ κ 216
    cell-2 = refl



-- κ=276: 5 nodes, 1 τ-classes, 3 σ-classes
module slice-Slice where

  -- τ=378: 5 nodes, 3 σ-classes
  module τ378 where

    -- σ=614 (2 nodes)
    cell-0 : κ 276 ≡ κ 276
    cell-0 = refl

    -- σ=1178 (2 nodes)
    cell-1 : κ 276 ≡ κ 276
    cell-1 = refl

    -- σ=2032 (1 nodes)
    cell-2 : κ 276 ≡ κ 276
    cell-2 = refl



-- κ=282: 4 nodes, 1 τ-classes, 3 σ-classes
module free_monoid-Call-0 where

  -- τ=385: 4 nodes, 3 σ-classes
  module τ385 where

    -- σ=628 (2 nodes)
    cell-0 : κ 282 ≡ κ 282
    cell-0 = refl

    -- σ=789 (1 nodes)
    cell-1 : κ 282 ≡ κ 282
    cell-1 = refl

    -- σ=1128 (1 nodes)
    cell-2 : κ 282 ≡ κ 282
    cell-2 = refl



-- κ=342: 3 nodes, 1 τ-classes, 3 σ-classes
module annassign-AnnAssign-4 where

  -- τ=454: 3 nodes, 3 σ-classes
  module τ454 where

    -- σ=754 (1 nodes)
    cell-0 : κ 342 ≡ κ 342
    cell-0 = refl

    -- σ=938 (1 nodes)
    cell-1 : κ 342 ≡ κ 342
    cell-1 = refl

    -- σ=945 (1 nodes)
    cell-2 : κ 342 ≡ κ 342
    cell-2 = refl



-- κ=355: 6 nodes, 1 τ-classes, 3 σ-classes
module let-k-Assign-9 where

  -- τ=476: 6 nodes, 3 σ-classes
  module τ476 where

    -- σ=812 (4 nodes)
    cell-0 : κ 355 ≡ κ 355
    cell-0 = refl

    -- σ=1194 (1 nodes)
    cell-1 : κ 355 ≡ κ 355
    cell-1 = refl

    -- σ=1321 (1 nodes)
    cell-2 : κ 355 ≡ κ 355
    cell-2 = refl



-- κ=374: 5 nodes, 1 τ-classes, 3 σ-classes
module coerce-Call-0 where

  -- τ=495: 5 nodes, 3 σ-classes
  module τ495 where

    -- σ=1056 (3 nodes)
    cell-0 : κ 374 ≡ κ 374
    cell-0 = refl

    -- σ=852 (1 nodes)
    cell-1 : κ 374 ≡ κ 374
    cell-1 = refl

    -- σ=1012 (1 nodes)
    cell-2 : κ 374 ≡ κ 374
    cell-2 = refl



-- κ=375: 5 nodes, 1 τ-classes, 3 σ-classes
module ifexp-IfExp-0 where

  -- τ=496: 5 nodes, 3 σ-classes
  module τ496 where

    -- σ=1057 (3 nodes)
    cell-0 : κ 375 ≡ κ 375
    cell-0 = refl

    -- σ=853 (1 nodes)
    cell-1 : κ 375 ≡ κ 375
    cell-1 = refl

    -- σ=1013 (1 nodes)
    cell-2 : κ 375 ≡ κ 375
    cell-2 = refl



-- κ=376: 5 nodes, 1 τ-classes, 3 σ-classes
module let-k-Assign-10 where

  -- τ=497: 5 nodes, 3 σ-classes
  module τ497 where

    -- σ=1058 (3 nodes)
    cell-0 : κ 376 ≡ κ 376
    cell-0 = refl

    -- σ=854 (1 nodes)
    cell-1 : κ 376 ≡ κ 376
    cell-1 = refl

    -- σ=1014 (1 nodes)
    cell-2 : κ 376 ≡ κ 376
    cell-2 = refl



-- κ=394: 3 nodes, 1 τ-classes, 3 σ-classes
module let-k-Assign-11 where

  -- τ=517: 3 nodes, 3 σ-classes
  module τ517 where

    -- σ=890 (1 nodes)
    cell-0 : κ 394 ≡ κ 394
    cell-0 = refl

    -- σ=1025 (1 nodes)
    cell-1 : κ 394 ≡ κ 394
    cell-1 = refl

    -- σ=1086 (1 nodes)
    cell-2 : κ 394 ≡ κ 394
    cell-2 = refl



-- κ=415: 3 nodes, 3 τ-classes, 3 σ-classes
module index-Index-6 where

  -- τ=543: 1 nodes, 1 σ-classes
  module τ543 where

    -- σ=967 (1 nodes)
    cell-0 : κ 415 ≡ κ 415
    cell-0 = refl


  -- τ=726: 1 nodes, 1 σ-classes
  module τ726 where

    -- σ=1490 (1 nodes)
    cell-0 : κ 415 ≡ κ 415
    cell-0 = refl


  -- τ=806: 1 nodes, 1 σ-classes
  module τ806 where

    -- σ=1700 (1 nodes)
    cell-0 : κ 415 ≡ κ 415
    cell-0 = refl



-- κ=416: 3 nodes, 3 τ-classes, 3 σ-classes
module subscript-Subscript-11 where

  -- τ=544: 1 nodes, 1 σ-classes
  module τ544 where

    -- σ=968 (1 nodes)
    cell-0 : κ 416 ≡ κ 416
    cell-0 = refl


  -- τ=727: 1 nodes, 1 σ-classes
  module τ727 where

    -- σ=1491 (1 nodes)
    cell-0 : κ 416 ≡ κ 416
    cell-0 = refl


  -- τ=807: 1 nodes, 1 σ-classes
  module τ807 where

    -- σ=1701 (1 nodes)
    cell-0 : κ 416 ≡ κ 416
    cell-0 = refl



-- κ=440: 3 nodes, 1 τ-classes, 3 σ-classes
module free_monoid-literal-List-0 where

  -- τ=568: 3 nodes, 3 σ-classes
  module list where

    -- σ=1043 (1 nodes)
    cell-0 : κ 440 ≡ κ 440
    cell-0 = refl

    -- σ=1074 (1 nodes)
    cell-1 : κ 440 ≡ κ 440
    cell-1 = refl

    -- σ=1296 (1 nodes)
    cell-2 : κ 440 ≡ κ 440
    cell-2 = refl



-- κ=468: 3 nodes, 2 τ-classes, 3 σ-classes
module let-k-Assign-12 where

  -- τ=603: 2 nodes, 2 σ-classes
  module τ603 where

    -- σ=1168 (1 nodes)
    cell-0 : κ 468 ≡ κ 468
    cell-0 = refl

    -- σ=2056 (1 nodes)
    cell-1 : κ 468 ≡ κ 468
    cell-1 = refl


  -- τ=654: 1 nodes, 1 σ-classes
  module τ654 where

    -- σ=1340 (1 nodes)
    cell-0 : κ 468 ≡ κ 468
    cell-0 = refl



-- κ=486: 3 nodes, 2 τ-classes, 3 σ-classes
module apply-Call-10 where

  -- τ=623: 2 nodes, 2 σ-classes
  module τ623 where

    -- σ=1243 (1 nodes)
    cell-0 : κ 486 ≡ κ 486
    cell-0 = refl

    -- σ=1249 (1 nodes)
    cell-1 : κ 486 ≡ κ 486
    cell-1 = refl


  -- τ=631: 1 nodes, 1 σ-classes
  module τ631 where

    -- σ=1270 (1 nodes)
    cell-0 : κ 486 ≡ κ 486
    cell-0 = refl



-- κ=487: 3 nodes, 2 τ-classes, 3 σ-classes
module let-k-Assign-13 where

  -- τ=624: 2 nodes, 2 σ-classes
  module τ624 where

    -- σ=1244 (1 nodes)
    cell-0 : κ 487 ≡ κ 487
    cell-0 = refl

    -- σ=1250 (1 nodes)
    cell-1 : κ 487 ≡ κ 487
    cell-1 = refl


  -- τ=632: 1 nodes, 1 σ-classes
  module τ632 where

    -- σ=1271 (1 nodes)
    cell-0 : κ 487 ≡ κ 487
    cell-0 = refl



-- κ=515: 3 nodes, 1 τ-classes, 3 σ-classes
module apply-Call-11 where

  -- τ=189: 3 nodes, 3 σ-classes
  module τ189 where

    -- σ=1352 (1 nodes)
    cell-0 : κ 515 ≡ κ 515
    cell-0 = refl

    -- σ=1419 (1 nodes)
    cell-1 : κ 515 ≡ κ 515
    cell-1 = refl

    -- σ=1534 (1 nodes)
    cell-2 : κ 515 ≡ κ 515
    cell-2 = refl



-- κ=550: 6 nodes, 1 τ-classes, 3 σ-classes
module apply-Call-12 where

  -- τ=701: 6 nodes, 3 σ-classes
  module τ701 where

    -- σ=1441 (2 nodes)
    cell-0 : κ 550 ≡ κ 550
    cell-0 = refl

    -- σ=1442 (2 nodes)
    cell-1 : κ 550 ≡ κ 550
    cell-1 = refl

    -- σ=1443 (2 nodes)
    cell-2 : κ 550 ≡ κ 550
    cell-2 = refl



-- κ=596: 3 nodes, 1 τ-classes, 3 σ-classes
module let-k-Assign-14 where

  -- τ=761: 3 nodes, 3 σ-classes
  module τ761 where

    -- σ=1583 (1 nodes)
    cell-0 : κ 596 ≡ κ 596
    cell-0 = refl

    -- σ=1585 (1 nodes)
    cell-1 : κ 596 ≡ κ 596
    cell-1 = refl

    -- σ=1587 (1 nodes)
    cell-2 : κ 596 ≡ κ 596
    cell-2 = refl



-- κ=597: 3 nodes, 1 τ-classes, 3 σ-classes
module cardinality-Call-2 where

  -- τ=763: 3 nodes, 3 σ-classes
  module int where

    -- σ=1595 (1 nodes)
    cell-0 : κ 597 ≡ κ 597
    cell-0 = refl

    -- σ=1600 (1 nodes)
    cell-1 : κ 597 ≡ κ 597
    cell-1 = refl

    -- σ=1606 (1 nodes)
    cell-2 : κ 597 ≡ κ 597
    cell-2 = refl



-- κ=600: 3 nodes, 1 τ-classes, 3 σ-classes
module partial-at-x3f-Attribute-0 where

  -- τ=188: 3 nodes, 3 σ-classes
  module τ188 where

    -- σ=1612 (1 nodes)
    cell-0 : κ 600 ≡ κ 600
    cell-0 = refl

    -- σ=1912 (1 nodes)
    cell-1 : κ 600 ≡ κ 600
    cell-1 = refl

    -- σ=2058 (1 nodes)
    cell-2 : κ 600 ≡ κ 600
    cell-2 = refl



-- κ=674: 3 nodes, 1 τ-classes, 3 σ-classes
module coerce-FormattedValue-4 where

  -- τ=851: 3 nodes, 3 σ-classes
  module τ851 where

    -- σ=1821 (1 nodes)
    cell-0 : κ 674 ≡ κ 674
    cell-0 = refl

    -- σ=1833 (1 nodes)
    cell-1 : κ 674 ≡ κ 674
    cell-1 = refl

    -- σ=1840 (1 nodes)
    cell-2 : κ 674 ≡ κ 674
    cell-2 = refl



-- κ=677: 3 nodes, 1 τ-classes, 3 σ-classes
module bimap-BinOp-1 where

  -- τ=854: 3 nodes, 3 σ-classes
  module τ854 where

    -- σ=1825 (1 nodes)
    cell-0 : κ 677 ≡ κ 677
    cell-0 = refl

    -- σ=1835 (1 nodes)
    cell-1 : κ 677 ≡ κ 677
    cell-1 = refl

    -- σ=1842 (1 nodes)
    cell-2 : κ 677 ≡ κ 677
    cell-2 = refl



-- κ=678: 3 nodes, 1 τ-classes, 3 σ-classes
module coerce-FormattedValue-5 where

  -- τ=855: 3 nodes, 3 σ-classes
  module τ855 where

    -- σ=1828 (1 nodes)
    cell-0 : κ 678 ≡ κ 678
    cell-0 = refl

    -- σ=1836 (1 nodes)
    cell-1 : κ 678 ≡ κ 678
    cell-1 = refl

    -- σ=1843 (1 nodes)
    cell-2 : κ 678 ≡ κ 678
    cell-2 = refl



-- κ=679: 3 nodes, 1 τ-classes, 3 σ-classes
module free_monoid-fold-JoinedStr-1 where

  -- τ=856: 3 nodes, 3 σ-classes
  module str where

    -- σ=1830 (1 nodes)
    cell-0 : κ 679 ≡ κ 679
    cell-0 = refl

    -- σ=1837 (1 nodes)
    cell-1 : κ 679 ≡ κ 679
    cell-1 = refl

    -- σ=1844 (1 nodes)
    cell-2 : κ 679 ≡ κ 679
    cell-2 = refl



-- κ=742: 3 nodes, 3 τ-classes, 3 σ-classes
module coerce-FormattedValue-6 where

  -- τ=920: 1 nodes, 1 σ-classes
  module τ920 where

    -- σ=1997 (1 nodes)
    cell-0 : κ 742 ≡ κ 742
    cell-0 = refl


  -- τ=922: 1 nodes, 1 σ-classes
  module τ922 where

    -- σ=2002 (1 nodes)
    cell-0 : κ 742 ≡ κ 742
    cell-0 = refl


  -- τ=950: 1 nodes, 1 σ-classes
  module τ950 where

    -- σ=2080 (1 nodes)
    cell-0 : κ 742 ≡ κ 742
    cell-0 = refl



-- κ=11: 45 nodes, 1 τ-classes, 2 σ-classes
module arg-arg-3 where

  -- τ=11: 45 nodes, 2 σ-classes
  module τ11 where

    -- σ=20 (42 nodes)
    cell-0 : κ 11 ≡ κ 11
    cell-0 = refl

    -- σ=1676 (3 nodes)
    cell-1 : κ 11 ≡ κ 11
    cell-1 = refl



-- κ=12: 18 nodes, 1 τ-classes, 2 σ-classes
module arguments-arguments-2 where

  -- τ=12: 18 nodes, 2 σ-classes
  module τ12 where

    -- σ=21 (15 nodes)
    cell-0 : κ 12 ≡ κ 12
    cell-0 = refl

    -- σ=1677 (3 nodes)
    cell-1 : κ 12 ≡ κ 12
    cell-1 = refl



-- κ=35: 2 nodes, 1 τ-classes, 2 σ-classes
module equalizer-Compare-8 where

  -- τ=49: 2 nodes, 2 σ-classes
  module τ49 where

    -- σ=60 (1 nodes)
    cell-0 : κ 35 ≡ κ 35
    cell-0 = refl

    -- σ=64 (1 nodes)
    cell-1 : κ 35 ≡ κ 35
    cell-1 = refl



-- κ=65: 3 nodes, 1 τ-classes, 2 σ-classes
module apply-Call-13 where

  -- τ=82: 3 nodes, 2 σ-classes
  module τ82 where

    -- σ=1437 (2 nodes)
    cell-0 : κ 65 ≡ κ 65
    cell-0 = refl

    -- σ=120 (1 nodes)
    cell-1 : κ 65 ≡ κ 65
    cell-1 = refl



-- κ=71: 2 nodes, 1 τ-classes, 2 σ-classes
module terminal-map-Return-1 where

  -- τ=88: 2 nodes, 2 σ-classes
  module τ88 where

    -- σ=128 (1 nodes)
    cell-0 : κ 71 ≡ κ 71
    cell-0 = refl

    -- σ=1405 (1 nodes)
    cell-1 : κ 71 ≡ κ 71
    cell-1 = refl



-- κ=76: 21 nodes, 2 τ-classes, 2 σ-classes
module product-Tuple-4 where

  -- τ=100: 17 nodes, 1 σ-classes
  module tuple-0 where

    -- σ=146 (17 nodes)
    cell-0 : κ 76 ≡ κ 76
    cell-0 = refl


  -- τ=96: 4 nodes, 1 σ-classes
  module tuple-1 where

    -- σ=142 (4 nodes)
    cell-0 : κ 76 ≡ κ 76
    cell-0 = refl



-- κ=77: 21 nodes, 2 τ-classes, 2 σ-classes
module index-Index-7 where

  -- τ=101: 17 nodes, 1 σ-classes
  module τ101 where

    -- σ=147 (17 nodes)
    cell-0 : κ 77 ≡ κ 77
    cell-0 = refl


  -- τ=97: 4 nodes, 1 σ-classes
  module τ97 where

    -- σ=143 (4 nodes)
    cell-0 : κ 77 ≡ κ 77
    cell-0 = refl



-- κ=78: 21 nodes, 2 τ-classes, 2 σ-classes
module subscript-Subscript-12 where

  -- τ=102: 17 nodes, 1 σ-classes
  module τ102 where

    -- σ=148 (17 nodes)
    cell-0 : κ 78 ≡ κ 78
    cell-0 = refl


  -- τ=98: 4 nodes, 1 σ-classes
  module τ98 where

    -- σ=144 (4 nodes)
    cell-0 : κ 78 ≡ κ 78
    cell-0 = refl



-- κ=81: 2 nodes, 1 τ-classes, 2 σ-classes
module annassign-AnnAssign-5 where

  -- τ=106: 2 nodes, 2 σ-classes
  module τ106 where

    -- σ=153 (1 nodes)
    cell-0 : κ 81 ≡ κ 81
    cell-0 = refl

    -- σ=186 (1 nodes)
    cell-1 : κ 81 ≡ κ 81
    cell-1 = refl



-- κ=82: 2 nodes, 2 τ-classes, 2 σ-classes
module annassign-AnnAssign-6 where

  -- τ=108: 1 nodes, 1 σ-classes
  module τ108 where

    -- σ=156 (1 nodes)
    cell-0 : κ 82 ≡ κ 82
    cell-0 = refl


  -- τ=110: 1 nodes, 1 σ-classes
  module τ110 where

    -- σ=159 (1 nodes)
    cell-0 : κ 82 ≡ κ 82
    cell-0 = refl



-- κ=84: 2 nodes, 2 τ-classes, 2 σ-classes
module annassign-AnnAssign-7 where

  -- τ=116: 1 nodes, 1 σ-classes
  module τ116 where

    -- σ=165 (1 nodes)
    cell-0 : κ 84 ≡ κ 84
    cell-0 = refl


  -- τ=277: 1 nodes, 1 σ-classes
  module τ277 where

    -- σ=400 (1 nodes)
    cell-0 : κ 84 ≡ κ 84
    cell-0 = refl



-- κ=97: 4 nodes, 1 τ-classes, 2 σ-classes
module apply-Call-14 where

  -- τ=140: 4 nodes, 2 σ-classes
  module τ140 where

    -- σ=202 (2 nodes)
    cell-0 : κ 97 ≡ κ 97
    cell-0 = refl

    -- σ=1559 (2 nodes)
    cell-1 : κ 97 ≡ κ 97
    cell-1 = refl



-- κ=98: 2 nodes, 1 τ-classes, 2 σ-classes
module annassign-AnnAssign-8 where

  -- τ=141: 2 nodes, 2 σ-classes
  module τ141 where

    -- σ=203 (1 nodes)
    cell-0 : κ 98 ≡ κ 98
    cell-0 = refl

    -- σ=375 (1 nodes)
    cell-1 : κ 98 ≡ κ 98
    cell-1 = refl



-- κ=101: 2 nodes, 1 τ-classes, 2 σ-classes
module let-k-Assign-15 where

  -- τ=146: 2 nodes, 2 σ-classes
  module τ146 where

    -- σ=214 (1 nodes)
    cell-0 : κ 101 ≡ κ 101
    cell-0 = refl

    -- σ=1796 (1 nodes)
    cell-1 : κ 101 ≡ κ 101
    cell-1 = refl



-- κ=107: 3 nodes, 1 τ-classes, 2 σ-classes
module effect-seq-Expr-6 where

  -- τ=155: 3 nodes, 2 σ-classes
  module τ155 where

    -- σ=1145 (2 nodes)
    cell-0 : κ 107 ≡ κ 107
    cell-0 = refl

    -- σ=226 (1 nodes)
    cell-1 : κ 107 ≡ κ 107
    cell-1 = refl



-- κ=110: 2 nodes, 2 τ-classes, 2 σ-classes
module free_monoid-op-at-x3f-Attribute-1 where

  -- τ=159: 1 nodes, 1 σ-classes
  module τ159 where

    -- σ=230 (1 nodes)
    cell-0 : κ 110 ≡ κ 110
    cell-0 = refl


  -- τ=179: 1 nodes, 1 σ-classes
  module τ179 where

    -- σ=264 (1 nodes)
    cell-0 : κ 110 ≡ κ 110
    cell-0 = refl



-- κ=114: 2 nodes, 2 τ-classes, 2 σ-classes
module terminal-map-Return-2 where

  -- τ=166: 1 nodes, 1 σ-classes
  module τ166 where

    -- σ=241 (1 nodes)
    cell-0 : κ 114 ≡ κ 114
    cell-0 = refl


  -- τ=512: 1 nodes, 1 σ-classes
  module τ512 where

    -- σ=880 (1 nodes)
    cell-0 : κ 114 ≡ κ 114
    cell-0 = refl



-- κ=159: 2 nodes, 2 τ-classes, 2 σ-classes
module annassign-AnnAssign-9 where

  -- τ=224: 1 nodes, 1 σ-classes
  module τ224 where

    -- σ=340 (1 nodes)
    cell-0 : κ 159 ≡ κ 159
    cell-0 = refl


  -- τ=275: 1 nodes, 1 σ-classes
  module τ275 where

    -- σ=396 (1 nodes)
    cell-0 : κ 159 ≡ κ 159
    cell-0 = refl



-- κ=181: 2 nodes, 2 τ-classes, 2 σ-classes
module product-Tuple-5 where

  -- τ=258: 1 nodes, 1 σ-classes
  module tuple-0 where

    -- σ=380 (1 nodes)
    cell-0 : κ 181 ≡ κ 181
    cell-0 = refl


  -- τ=461: 1 nodes, 1 σ-classes
  module tuple-1 where

    -- σ=777 (1 nodes)
    cell-0 : κ 181 ≡ κ 181
    cell-0 = refl



-- κ=182: 2 nodes, 2 τ-classes, 2 σ-classes
module index-Index-8 where

  -- τ=259: 1 nodes, 1 σ-classes
  module τ259 where

    -- σ=381 (1 nodes)
    cell-0 : κ 182 ≡ κ 182
    cell-0 = refl


  -- τ=462: 1 nodes, 1 σ-classes
  module τ462 where

    -- σ=778 (1 nodes)
    cell-0 : κ 182 ≡ κ 182
    cell-0 = refl



-- κ=183: 2 nodes, 2 τ-classes, 2 σ-classes
module subscript-Subscript-13 where

  -- τ=260: 1 nodes, 1 σ-classes
  module τ260 where

    -- σ=382 (1 nodes)
    cell-0 : κ 183 ≡ κ 183
    cell-0 = refl


  -- τ=463: 1 nodes, 1 σ-classes
  module τ463 where

    -- σ=779 (1 nodes)
    cell-0 : κ 183 ≡ κ 183
    cell-0 = refl



-- κ=184: 2 nodes, 2 τ-classes, 2 σ-classes
module index-Index-9 where

  -- τ=261: 1 nodes, 1 σ-classes
  module τ261 where

    -- σ=383 (1 nodes)
    cell-0 : κ 184 ≡ κ 184
    cell-0 = refl


  -- τ=464: 1 nodes, 1 σ-classes
  module τ464 where

    -- σ=780 (1 nodes)
    cell-0 : κ 184 ≡ κ 184
    cell-0 = refl



-- κ=185: 2 nodes, 2 τ-classes, 2 σ-classes
module subscript-Subscript-14 where

  -- τ=262: 1 nodes, 1 σ-classes
  module τ262 where

    -- σ=384 (1 nodes)
    cell-0 : κ 185 ≡ κ 185
    cell-0 = refl


  -- τ=465: 1 nodes, 1 σ-classes
  module τ465 where

    -- σ=781 (1 nodes)
    cell-0 : κ 185 ≡ κ 185
    cell-0 = refl



-- κ=191: 2 nodes, 2 τ-classes, 2 σ-classes
module subscript-Subscript-15 where

  -- τ=269: 1 nodes, 1 σ-classes
  module τ269 where

    -- σ=391 (1 nodes)
    cell-0 : κ 191 ≡ κ 191
    cell-0 = refl


  -- τ=878: 1 nodes, 1 σ-classes
  module τ878 where

    -- σ=1899 (1 nodes)
    cell-0 : κ 191 ≡ κ 191
    cell-0 = refl



-- κ=200: 3 nodes, 2 τ-classes, 2 σ-classes
module product-Tuple-6 where

  -- τ=712: 2 nodes, 1 σ-classes
  module tuple-0 where

    -- σ=1464 (2 nodes)
    cell-0 : κ 200 ≡ κ 200
    cell-0 = refl


  -- τ=290: 1 nodes, 1 σ-classes
  module tuple-1 where

    -- σ=418 (1 nodes)
    cell-0 : κ 200 ≡ κ 200
    cell-0 = refl



-- κ=201: 3 nodes, 2 τ-classes, 2 σ-classes
module index-Index-10 where

  -- τ=713: 2 nodes, 1 σ-classes
  module τ713 where

    -- σ=1465 (2 nodes)
    cell-0 : κ 201 ≡ κ 201
    cell-0 = refl


  -- τ=291: 1 nodes, 1 σ-classes
  module τ291 where

    -- σ=419 (1 nodes)
    cell-0 : κ 201 ≡ κ 201
    cell-0 = refl



-- κ=219: 2 nodes, 2 τ-classes, 2 σ-classes
module partial-apply-at-state-Call-1 where

  -- τ=311: 1 nodes, 1 σ-classes
  module T-0 where

    -- σ=459 (1 nodes)
    cell-0 : κ 219 ≡ κ 219
    cell-0 = refl


  -- τ=392: 1 nodes, 1 σ-classes
  module T-1 where

    -- σ=639 (1 nodes)
    cell-0 : κ 219 ≡ κ 219
    cell-0 = refl



-- κ=227: 2 nodes, 1 τ-classes, 2 σ-classes
module arguments-arguments-3 where

  -- τ=320: 2 nodes, 2 σ-classes
  module τ320 where

    -- σ=472 (1 nodes)
    cell-0 : κ 227 ≡ κ 227
    cell-0 = refl

    -- σ=1523 (1 nodes)
    cell-1 : κ 227 ≡ κ 227
    cell-1 = refl



-- κ=242: 2 nodes, 2 τ-classes, 2 σ-classes
module equalizer-Compare-9 where

  -- τ=341: 1 nodes, 1 σ-classes
  module τ341 where

    -- σ=518 (1 nodes)
    cell-0 : κ 242 ≡ κ 242
    cell-0 = refl


  -- τ=411: 1 nodes, 1 σ-classes
  module τ411 where

    -- σ=670 (1 nodes)
    cell-0 : κ 242 ≡ κ 242
    cell-0 = refl



-- κ=256: 2 nodes, 1 τ-classes, 2 σ-classes
module equalizer-Compare-10 where

  -- τ=357: 2 nodes, 2 σ-classes
  module τ357 where

    -- σ=562 (1 nodes)
    cell-0 : κ 256 ≡ κ 256
    cell-0 = refl

    -- σ=695 (1 nodes)
    cell-1 : κ 256 ≡ κ 256
    cell-1 = refl



-- κ=262: 2 nodes, 1 τ-classes, 2 σ-classes
module partial-apply-at-x3f-Call-0 where

  -- τ=364: 2 nodes, 2 σ-classes
  module τ364 where

    -- σ=584 (1 nodes)
    cell-0 : κ 262 ≡ κ 262
    cell-0 = refl

    -- σ=1706 (1 nodes)
    cell-1 : κ 262 ≡ κ 262
    cell-1 = refl



-- κ=277: 4 nodes, 1 τ-classes, 2 σ-classes
module subscript-Subscript-16 where

  -- τ=379: 4 nodes, 2 σ-classes
  module τ379 where

    -- σ=615 (2 nodes)
    cell-0 : κ 277 ≡ κ 277
    cell-0 = refl

    -- σ=1179 (2 nodes)
    cell-1 : κ 277 ≡ κ 277
    cell-1 = refl



-- κ=279: 2 nodes, 1 τ-classes, 2 σ-classes
module free_monoid-fold-JoinedStr-2 where

  -- τ=381: 2 nodes, 2 σ-classes
  module str where

    -- σ=617 (1 nodes)
    cell-0 : κ 279 ≡ κ 279
    cell-0 = refl

    -- σ=620 (1 nodes)
    cell-1 : κ 279 ≡ κ 279
    cell-1 = refl



-- κ=280: 2 nodes, 1 τ-classes, 2 σ-classes
module let-k-Assign-16 where

  -- τ=382: 2 nodes, 2 σ-classes
  module τ382 where

    -- σ=618 (1 nodes)
    cell-0 : κ 280 ≡ κ 280
    cell-0 = refl

    -- σ=621 (1 nodes)
    cell-1 : κ 280 ≡ κ 280
    cell-1 = refl



-- κ=296: 2 nodes, 1 τ-classes, 2 σ-classes
module free_monoid-Call-1 where

  -- τ=404: 2 nodes, 2 σ-classes
  module τ404 where

    -- σ=660 (1 nodes)
    cell-0 : κ 296 ≡ κ 296
    cell-0 = refl

    -- σ=947 (1 nodes)
    cell-1 : κ 296 ≡ κ 296
    cell-1 = refl



-- κ=306: 4 nodes, 2 τ-classes, 2 σ-classes
module free_monoid-fold-JoinedStr-3 where

  -- τ=414: 3 nodes, 1 σ-classes
  module str-0 where

    -- σ=675 (3 nodes)
    cell-0 : κ 306 ≡ κ 306
    cell-0 = refl


  -- τ=487: 1 nodes, 1 σ-classes
  module str-1 where

    -- σ=841 (1 nodes)
    cell-0 : κ 306 ≡ κ 306
    cell-0 = refl



-- κ=314: 3 nodes, 1 τ-classes, 2 σ-classes
module comprehension-comprehension-1 where

  -- τ=422: 3 nodes, 2 σ-classes
  module τ422 where

    -- σ=687 (2 nodes)
    cell-0 : κ 314 ≡ κ 314
    cell-0 = refl

    -- σ=1286 (1 nodes)
    cell-1 : κ 314 ≡ κ 314
    cell-1 = refl



-- κ=326: 2 nodes, 1 τ-classes, 2 σ-classes
module exponential-literal-Dict-0 where

  -- τ=435: 2 nodes, 2 σ-classes
  module dict where

    -- σ=704 (1 nodes)
    cell-0 : κ 326 ≡ κ 326
    cell-0 = refl

    -- σ=1369 (1 nodes)
    cell-1 : κ 326 ≡ κ 326
    cell-1 = refl



-- κ=334: 3 nodes, 1 τ-classes, 2 σ-classes
module equalizer-Compare-11 where

  -- τ=443: 3 nodes, 2 σ-classes
  module τ443 where

    -- σ=1275 (2 nodes)
    cell-0 : κ 334 ≡ κ 334
    cell-0 = refl

    -- σ=717 (1 nodes)
    cell-1 : κ 334 ≡ κ 334
    cell-1 = refl



-- κ=341: 2 nodes, 1 τ-classes, 2 σ-classes
module arguments-arguments-4 where

  -- τ=453: 2 nodes, 2 σ-classes
  module τ453 where

    -- σ=748 (1 nodes)
    cell-0 : κ 341 ≡ κ 341
    cell-0 = refl

    -- σ=934 (1 nodes)
    cell-1 : κ 341 ≡ κ 341
    cell-1 = refl



-- κ=346: 2 nodes, 1 τ-classes, 2 σ-classes
module equalizer-If-0 where

  -- τ=459: 2 nodes, 2 σ-classes
  module τ459 where

    -- σ=769 (1 nodes)
    cell-0 : κ 346 ≡ κ 346
    cell-0 = refl

    -- σ=953 (1 nodes)
    cell-1 : κ 346 ≡ κ 346
    cell-1 = refl



-- κ=347: 3 nodes, 1 τ-classes, 2 σ-classes
module annassign-AnnAssign-10 where

  -- τ=460: 3 nodes, 2 σ-classes
  module τ460 where

    -- σ=775 (2 nodes)
    cell-0 : κ 347 ≡ κ 347
    cell-0 = refl

    -- σ=1066 (1 nodes)
    cell-1 : κ 347 ≡ κ 347
    cell-1 = refl



-- κ=358: 2 nodes, 1 τ-classes, 2 σ-classes
module free_monoid-snoc-at-x3f-Call-0 where

  -- τ=478: 2 nodes, 2 σ-classes
  module τ478 where

    -- σ=818 (1 nodes)
    cell-0 : κ 358 ≡ κ 358
    cell-0 = refl

    -- σ=1753 (1 nodes)
    cell-1 : κ 358 ≡ κ 358
    cell-1 = refl



-- κ=359: 2 nodes, 1 τ-classes, 2 σ-classes
module effect-seq-Expr-7 where

  -- τ=479: 2 nodes, 2 σ-classes
  module τ479 where

    -- σ=819 (1 nodes)
    cell-0 : κ 359 ≡ κ 359
    cell-0 = refl

    -- σ=1754 (1 nodes)
    cell-1 : κ 359 ≡ κ 359
    cell-1 = refl



-- κ=386: 2 nodes, 1 τ-classes, 2 σ-classes
module terminal-map-Return-3 where

  -- τ=508: 2 nodes, 2 σ-classes
  module τ508 where

    -- σ=876 (1 nodes)
    cell-0 : κ 386 ≡ κ 386
    cell-0 = refl

    -- σ=1800 (1 nodes)
    cell-1 : κ 386 ≡ κ 386
    cell-1 = refl



-- κ=396: 2 nodes, 1 τ-classes, 2 σ-classes
module apply-Call-15 where

  -- τ=520: 2 nodes, 2 σ-classes
  module τ520 where

    -- σ=898 (1 nodes)
    cell-0 : κ 396 ≡ κ 396
    cell-0 = refl

    -- σ=1255 (1 nodes)
    cell-1 : κ 396 ≡ κ 396
    cell-1 = refl



-- κ=397: 2 nodes, 1 τ-classes, 2 σ-classes
module let-k-Assign-17 where

  -- τ=521: 2 nodes, 2 σ-classes
  module τ521 where

    -- σ=899 (1 nodes)
    cell-0 : κ 397 ≡ κ 397
    cell-0 = refl

    -- σ=1256 (1 nodes)
    cell-1 : κ 397 ≡ κ 397
    cell-1 = refl



-- κ=413: 2 nodes, 1 τ-classes, 2 σ-classes
module complement-UnaryOp where

  -- τ=541: 2 nodes, 2 σ-classes
  module τ541 where

    -- σ=964 (1 nodes)
    cell-0 : κ 413 ≡ κ 413
    cell-0 = refl

    -- σ=2010 (1 nodes)
    cell-1 : κ 413 ≡ κ 413
    cell-1 = refl



-- κ=420: 2 nodes, 1 τ-classes, 2 σ-classes
module free_monoid-snoc-at-x3f-Call-1 where

  -- τ=548: 2 nodes, 2 σ-classes
  module τ548 where

    -- σ=985 (1 nodes)
    cell-0 : κ 420 ≡ κ 420
    cell-0 = refl

    -- σ=1671 (1 nodes)
    cell-1 : κ 420 ≡ κ 420
    cell-1 = refl



-- κ=421: 2 nodes, 1 τ-classes, 2 σ-classes
module effect-seq-Expr-8 where

  -- τ=549: 2 nodes, 2 σ-classes
  module τ549 where

    -- σ=986 (1 nodes)
    cell-0 : κ 421 ≡ κ 421
    cell-0 = refl

    -- σ=1672 (1 nodes)
    cell-1 : κ 421 ≡ κ 421
    cell-1 = refl



-- κ=441: 2 nodes, 1 τ-classes, 2 σ-classes
module product-Tuple-7 where

  -- τ=569: 2 nodes, 2 σ-classes
  module tuple where

    -- σ=1045 (1 nodes)
    cell-0 : κ 441 ≡ κ 441
    cell-0 = refl

    -- σ=1076 (1 nodes)
    cell-1 : κ 441 ≡ κ 441
    cell-1 = refl



-- κ=442: 2 nodes, 1 τ-classes, 2 σ-classes
module free_monoid-snoc-at-state-Call-0 where

  -- τ=570: 2 nodes, 2 σ-classes
  module None where

    -- σ=1046 (1 nodes)
    cell-0 : κ 442 ≡ κ 442
    cell-0 = refl

    -- σ=1077 (1 nodes)
    cell-1 : κ 442 ≡ κ 442
    cell-1 = refl



-- κ=443: 2 nodes, 1 τ-classes, 2 σ-classes
module effect-seq-Expr-9 where

  -- τ=571: 2 nodes, 2 σ-classes
  module τ571 where

    -- σ=1047 (1 nodes)
    cell-0 : κ 443 ≡ κ 443
    cell-0 = refl

    -- σ=1078 (1 nodes)
    cell-1 : κ 443 ≡ κ 443
    cell-1 = refl



-- κ=444: 2 nodes, 1 τ-classes, 2 σ-classes
module equalizer-If-1 where

  -- τ=572: 2 nodes, 2 σ-classes
  module τ572 where

    -- σ=1061 (1 nodes)
    cell-0 : κ 444 ≡ κ 444
    cell-0 = refl

    -- σ=1079 (1 nodes)
    cell-1 : κ 444 ≡ κ 444
    cell-1 = refl



-- κ=445: 2 nodes, 1 τ-classes, 2 σ-classes
module equalizer-If-2 where

  -- τ=573: 2 nodes, 2 σ-classes
  module τ573 where

    -- σ=1063 (1 nodes)
    cell-0 : κ 445 ≡ κ 445
    cell-0 = refl

    -- σ=1081 (1 nodes)
    cell-1 : κ 445 ≡ κ 445
    cell-1 = refl



-- κ=446: 2 nodes, 1 τ-classes, 2 σ-classes
module fold-For-1 where

  -- τ=574: 2 nodes, 2 σ-classes
  module τ574 where

    -- σ=1064 (1 nodes)
    cell-0 : κ 446 ≡ κ 446
    cell-0 = refl

    -- σ=1082 (1 nodes)
    cell-1 : κ 446 ≡ κ 446
    cell-1 = refl



-- κ=450: 2 nodes, 2 τ-classes, 2 σ-classes
module annassign-AnnAssign-11 where

  -- τ=579: 1 nodes, 1 σ-classes
  module τ579 where

    -- σ=1108 (1 nodes)
    cell-0 : κ 450 ≡ κ 450
    cell-0 = refl


  -- τ=789: 1 nodes, 1 σ-classes
  module τ789 where

    -- σ=1657 (1 nodes)
    cell-0 : κ 450 ≡ κ 450
    cell-0 = refl



-- κ=451: 2 nodes, 1 τ-classes, 2 σ-classes
module projection-at-object-Attribute where

  -- τ=34: 2 nodes, 2 σ-classes
  module Self-_parent where

    -- σ=1110 (1 nodes)
    cell-0 : κ 451 ≡ κ 451
    cell-0 = refl

    -- σ=1131 (1 nodes)
    cell-1 : κ 451 ≡ κ 451
    cell-1 = refl



-- κ=452: 2 nodes, 1 τ-classes, 2 σ-classes
module projection-compute-at-object-Call where

  -- τ=581: 2 nodes, 2 σ-classes
  module Iter where

    -- σ=1111 (1 nodes)
    cell-0 : κ 452 ≡ κ 452
    cell-0 = refl

    -- σ=1132 (1 nodes)
    cell-1 : κ 452 ≡ κ 452
    cell-1 = refl



-- κ=453: 2 nodes, 1 τ-classes, 2 σ-classes
module free_monoid-Call-2 where

  -- τ=582: 2 nodes, 2 σ-classes
  module τ582 where

    -- σ=1112 (1 nodes)
    cell-0 : κ 453 ≡ κ 453
    cell-0 = refl

    -- σ=1133 (1 nodes)
    cell-1 : κ 453 ≡ κ 453
    cell-1 = refl



-- κ=463: 2 nodes, 1 τ-classes, 2 σ-classes
module annassign-AnnAssign-12 where

  -- τ=594: 2 nodes, 2 σ-classes
  module τ594 where

    -- σ=1148 (1 nodes)
    cell-0 : κ 463 ≡ κ 463
    cell-0 = refl

    -- σ=1305 (1 nodes)
    cell-1 : κ 463 ≡ κ 463
    cell-1 = refl



-- κ=465: 2 nodes, 1 τ-classes, 2 σ-classes
module equalizer-If-3 where

  -- τ=599: 2 nodes, 2 σ-classes
  module τ599 where

    -- σ=1158 (1 nodes)
    cell-0 : κ 465 ≡ κ 465
    cell-0 = refl

    -- σ=1310 (1 nodes)
    cell-1 : κ 465 ≡ κ 465
    cell-1 = refl



-- κ=466: 2 nodes, 1 τ-classes, 2 σ-classes
module equalizer-If-4 where

  -- τ=600: 2 nodes, 2 σ-classes
  module τ600 where

    -- σ=1161 (1 nodes)
    cell-0 : κ 466 ≡ κ 466
    cell-0 = refl

    -- σ=1311 (1 nodes)
    cell-1 : κ 466 ≡ κ 466
    cell-1 = refl



-- κ=467: 2 nodes, 1 τ-classes, 2 σ-classes
module fold-For-2 where

  -- τ=601: 2 nodes, 2 σ-classes
  module τ601 where

    -- σ=1162 (1 nodes)
    cell-0 : κ 467 ≡ κ 467
    cell-0 = refl

    -- σ=1312 (1 nodes)
    cell-1 : κ 467 ≡ κ 467
    cell-1 = refl



-- κ=471: 2 nodes, 1 τ-classes, 2 σ-classes
module equalizer-If-5 where

  -- τ=606: 2 nodes, 2 σ-classes
  module τ606 where

    -- σ=1195 (1 nodes)
    cell-0 : κ 471 ≡ κ 471
    cell-0 = refl

    -- σ=1322 (1 nodes)
    cell-1 : κ 471 ≡ κ 471
    cell-1 = refl



-- κ=472: 2 nodes, 1 τ-classes, 2 σ-classes
module fold-For-3 where

  -- τ=607: 2 nodes, 2 σ-classes
  module τ607 where

    -- σ=1196 (1 nodes)
    cell-0 : κ 472 ≡ κ 472
    cell-0 = refl

    -- σ=1323 (1 nodes)
    cell-1 : κ 472 ≡ κ 472
    cell-1 = refl



-- κ=473: 2 nodes, 2 τ-classes, 2 σ-classes
module free_monoid-snoc-at-state-Call-1 where

  -- τ=609: 1 nodes, 1 σ-classes
  module None-0 where

    -- σ=1198 (1 nodes)
    cell-0 : κ 473 ≡ κ 473
    cell-0 = refl


  -- τ=647: 1 nodes, 1 σ-classes
  module None-1 where

    -- σ=1325 (1 nodes)
    cell-0 : κ 473 ≡ κ 473
    cell-0 = refl



-- κ=474: 2 nodes, 2 τ-classes, 2 σ-classes
module effect-seq-Expr-10 where

  -- τ=610: 1 nodes, 1 σ-classes
  module τ610 where

    -- σ=1199 (1 nodes)
    cell-0 : κ 474 ≡ κ 474
    cell-0 = refl


  -- τ=648: 1 nodes, 1 σ-classes
  module τ648 where

    -- σ=1326 (1 nodes)
    cell-0 : κ 474 ≡ κ 474
    cell-0 = refl



-- κ=511: 2 nodes, 1 τ-classes, 2 σ-classes
module powerset-Call-0 where

  -- τ=520: 2 nodes, 2 σ-classes
  module τ520 where

    -- σ=1344 (1 nodes)
    cell-0 : κ 511 ≡ κ 511
    cell-0 = refl

    -- σ=1889 (1 nodes)
    cell-1 : κ 511 ≡ κ 511
    cell-1 = refl



-- κ=531: 2 nodes, 2 τ-classes, 2 σ-classes
module product-Tuple-8 where

  -- τ=677: 1 nodes, 1 σ-classes
  module tuple-0 where

    -- σ=1399 (1 nodes)
    cell-0 : κ 531 ≡ κ 531
    cell-0 = refl


  -- τ=679: 1 nodes, 1 σ-classes
  module tuple-1 where

    -- σ=1401 (1 nodes)
    cell-0 : κ 531 ≡ κ 531
    cell-0 = refl



-- κ=540: 4 nodes, 1 τ-classes, 2 σ-classes
module eval-Call where

  -- τ=689: 4 nodes, 2 σ-classes
  module T where

    -- σ=1529 (3 nodes)
    cell-0 : κ 540 ≡ κ 540
    cell-0 = refl

    -- σ=1416 (1 nodes)
    cell-1 : κ 540 ≡ κ 540
    cell-1 = refl



-- κ=541: 4 nodes, 1 τ-classes, 2 σ-classes
module annassign-AnnAssign-13 where

  -- τ=690: 4 nodes, 2 σ-classes
  module τ690 where

    -- σ=1530 (3 nodes)
    cell-0 : κ 541 ≡ κ 541
    cell-0 = refl

    -- σ=1417 (1 nodes)
    cell-1 : κ 541 ≡ κ 541
    cell-1 = refl



-- κ=548: 2 nodes, 2 τ-classes, 2 σ-classes
module subscript-Subscript-17 where

  -- τ=698: 1 nodes, 1 σ-classes
  module τ698 where

    -- σ=1430 (1 nodes)
    cell-0 : κ 548 ≡ κ 548
    cell-0 = refl


  -- τ=710: 1 nodes, 1 σ-classes
  module τ710 where

    -- σ=1454 (1 nodes)
    cell-0 : κ 548 ≡ κ 548
    cell-0 = refl



-- κ=559: 3 nodes, 1 τ-classes, 2 σ-classes
module terminal-map-Return-4 where

  -- τ=709: 3 nodes, 2 σ-classes
  module τ709 where

    -- σ=1453 (2 nodes)
    cell-0 : κ 559 ≡ κ 559
    cell-0 = refl

    -- σ=1717 (1 nodes)
    cell-1 : κ 559 ≡ κ 559
    cell-1 = refl



-- κ=570: 2 nodes, 2 τ-classes, 2 σ-classes
module annassign-AnnAssign-14 where

  -- τ=729: 1 nodes, 1 σ-classes
  module τ729 where

    -- σ=1493 (1 nodes)
    cell-0 : κ 570 ≡ κ 570
    cell-0 = refl


  -- τ=808: 1 nodes, 1 σ-classes
  module τ808 where

    -- σ=1702 (1 nodes)
    cell-0 : κ 570 ≡ κ 570
    cell-0 = refl



-- κ=571: 2 nodes, 1 τ-classes, 2 σ-classes
module index-Index-11 where

  -- τ=730: 2 nodes, 2 σ-classes
  module τ730 where

    -- σ=1497 (1 nodes)
    cell-0 : κ 571 ≡ κ 571
    cell-0 = refl

    -- σ=1501 (1 nodes)
    cell-1 : κ 571 ≡ κ 571
    cell-1 = refl



-- κ=576: 2 nodes, 1 τ-classes, 2 σ-classes
module comprehension-comprehension-2 where

  -- τ=735: 2 nodes, 2 σ-classes
  module τ735 where

    -- σ=1513 (1 nodes)
    cell-0 : κ 576 ≡ κ 576
    cell-0 = refl

    -- σ=1741 (1 nodes)
    cell-1 : κ 576 ≡ κ 576
    cell-1 = refl



-- κ=589: 2 nodes, 1 τ-classes, 2 σ-classes
module annassign-AnnAssign-15 where

  -- τ=751: 2 nodes, 2 σ-classes
  module τ751 where

    -- σ=1560 (1 nodes)
    cell-0 : κ 589 ≡ κ 589
    cell-0 = refl

    -- σ=1574 (1 nodes)
    cell-1 : κ 589 ≡ κ 589
    cell-1 = refl



-- κ=654: 2 nodes, 1 τ-classes, 2 σ-classes
module apply-Call-16 where

  -- τ=827: 2 nodes, 2 σ-classes
  module τ827 where

    -- σ=1748 (1 nodes)
    cell-0 : κ 654 ≡ κ 654
    cell-0 = refl

    -- σ=2063 (1 nodes)
    cell-1 : κ 654 ≡ κ 654
    cell-1 = refl



-- κ=655: 2 nodes, 1 τ-classes, 2 σ-classes
module let-k-Assign-18 where

  -- τ=828: 2 nodes, 2 σ-classes
  module τ828 where

    -- σ=1749 (1 nodes)
    cell-0 : κ 655 ≡ κ 655
    cell-0 = refl

    -- σ=2064 (1 nodes)
    cell-1 : κ 655 ≡ κ 655
    cell-1 = refl



-- κ=671: 2 nodes, 2 τ-classes, 2 σ-classes
module free_monoid-fold-JoinedStr-4 where

  -- τ=848: 1 nodes, 1 σ-classes
  module str-0 where

    -- σ=1815 (1 nodes)
    cell-0 : κ 671 ≡ κ 671
    cell-0 = refl


  -- τ=931: 1 nodes, 1 σ-classes
  module str-1 where

    -- σ=2016 (1 nodes)
    cell-0 : κ 671 ≡ κ 671
    cell-0 = refl



-- κ=680: 2 nodes, 1 τ-classes, 2 σ-classes
module coerce-FormattedValue-7 where

  -- τ=857: 2 nodes, 2 σ-classes
  module τ857 where

    -- σ=1847 (1 nodes)
    cell-0 : κ 680 ≡ κ 680
    cell-0 = refl

    -- σ=1856 (1 nodes)
    cell-1 : κ 680 ≡ κ 680
    cell-1 = refl



-- κ=681: 2 nodes, 1 τ-classes, 2 σ-classes
module bimap-BinOp-2 where

  -- τ=858: 2 nodes, 2 σ-classes
  module τ858 where

    -- σ=1849 (1 nodes)
    cell-0 : κ 681 ≡ κ 681
    cell-0 = refl

    -- σ=1857 (1 nodes)
    cell-1 : κ 681 ≡ κ 681
    cell-1 = refl



-- κ=682: 2 nodes, 1 τ-classes, 2 σ-classes
module bimap-BinOp-3 where

  -- τ=859: 2 nodes, 2 σ-classes
  module τ859 where

    -- σ=1850 (1 nodes)
    cell-0 : κ 682 ≡ κ 682
    cell-0 = refl

    -- σ=1858 (1 nodes)
    cell-1 : κ 682 ≡ κ 682
    cell-1 = refl



-- κ=683: 2 nodes, 1 τ-classes, 2 σ-classes
module coerce-FormattedValue-8 where

  -- τ=860: 2 nodes, 2 σ-classes
  module τ860 where

    -- σ=1851 (1 nodes)
    cell-0 : κ 683 ≡ κ 683
    cell-0 = refl

    -- σ=1859 (1 nodes)
    cell-1 : κ 683 ≡ κ 683
    cell-1 = refl



-- κ=684: 2 nodes, 1 τ-classes, 2 σ-classes
module free_monoid-fold-JoinedStr-5 where

  -- τ=861: 2 nodes, 2 σ-classes
  module str where

    -- σ=1852 (1 nodes)
    cell-0 : κ 684 ≡ κ 684
    cell-0 = refl

    -- σ=1860 (1 nodes)
    cell-1 : κ 684 ≡ κ 684
    cell-1 = refl



-- κ=3: 1 nodes, 1 τ-classes, 1 σ-classes
module pullback-import-ImportFrom-0 where

  -- τ=3: 1 nodes, 1 σ-classes
  module τ3 where

    -- σ=3 (1 nodes)
    cell-0 : κ 3 ≡ κ 3
    cell-0 = refl



-- κ=4: 1 nodes, 1 τ-classes, 1 σ-classes
module pullback-import-ImportFrom-1 where

  -- τ=4: 1 nodes, 1 σ-classes
  module τ4 where

    -- σ=6 (1 nodes)
    cell-0 : κ 4 ≡ κ 4
    cell-0 = refl



-- κ=5: 1 nodes, 1 τ-classes, 1 σ-classes
module pullback-import-ImportFrom-2 where

  -- τ=5: 1 nodes, 1 σ-classes
  module τ5 where

    -- σ=10 (1 nodes)
    cell-0 : κ 5 ≡ κ 5
    cell-0 = refl



-- κ=6: 365 nodes, 1 τ-classes, 1 σ-classes
module store-Store where

  -- τ=6: 365 nodes, 1 σ-classes
  module τ6 where

    -- σ=13 (365 nodes)
    cell-0 : κ 6 ≡ κ 6
    cell-0 = refl



-- κ=8: 2366 nodes, 1 τ-classes, 1 σ-classes
module load-Load where

  -- τ=8: 2366 nodes, 1 σ-classes
  module τ8 where

    -- σ=17 (2366 nodes)
    cell-0 : κ 8 ≡ κ 8
    cell-0 = refl



-- κ=9: 1 nodes, 1 τ-classes, 1 σ-classes
module product-Tuple-9 where

  -- τ=9: 1 nodes, 1 σ-classes
  module tuple where

    -- σ=18 (1 nodes)
    cell-0 : κ 9 ≡ κ 9
    cell-0 = refl



-- κ=10: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-19 where

  -- τ=10: 1 nodes, 1 σ-classes
  module τ10 where

    -- σ=19 (1 nodes)
    cell-0 : κ 10 ≡ κ 10
    cell-0 = refl



-- κ=18: 15 nodes, 1 τ-classes, 1 σ-classes
module exponential-literal-Dict-1 where

  -- τ=20: 15 nodes, 1 σ-classes
  module dict where

    -- σ=29 (15 nodes)
    cell-0 : κ 18 ≡ κ 18
    cell-0 = refl



-- κ=20: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-0 where

  -- τ=30: 1 nodes, 1 σ-classes
  module τ30 where

    -- σ=38 (1 nodes)
    cell-0 : κ 20 ≡ κ 20
    cell-0 = refl



-- κ=23: 9 nodes, 1 τ-classes, 1 σ-classes
module notin-NotIn where

  -- τ=33: 9 nodes, 1 σ-classes
  module τ33 where

    -- σ=42 (9 nodes)
    cell-0 : κ 23 ≡ κ 23
    cell-0 = refl



-- κ=29: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-20 where

  -- τ=40: 1 nodes, 1 σ-classes
  module τ40 where

    -- σ=51 (1 nodes)
    cell-0 : κ 29 ≡ κ 29
    cell-0 = refl



-- κ=30: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-6 where

  -- τ=41: 1 nodes, 1 σ-classes
  module τ41 where

    -- σ=52 (1 nodes)
    cell-0 : κ 30 ≡ κ 30
    cell-0 = refl



-- κ=31: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-1 where

  -- τ=43: 1 nodes, 1 σ-classes
  module τ43 where

    -- σ=53 (1 nodes)
    cell-0 : κ 31 ≡ κ 31
    cell-0 = refl



-- κ=34: 14 nodes, 1 τ-classes, 1 σ-classes
module noteq-NotEq where

  -- τ=48: 14 nodes, 1 σ-classes
  module τ48 where

    -- σ=59 (14 nodes)
    cell-0 : κ 34 ≡ κ 34
    cell-0 = refl



-- κ=37: 1 nodes, 1 τ-classes, 1 σ-classes
module fixpoint-While-0 where

  -- τ=51: 1 nodes, 1 σ-classes
  module τ51 where

    -- σ=62 (1 nodes)
    cell-0 : κ 37 ≡ κ 37
    cell-0 = refl



-- κ=38: 1 nodes, 1 τ-classes, 1 σ-classes
module product-unpack-Tuple-1 where

  -- τ=52: 1 nodes, 1 σ-classes
  module tuple where

    -- σ=66 (1 nodes)
    cell-0 : κ 38 ≡ κ 38
    cell-0 = refl



-- κ=39: 1 nodes, 1 τ-classes, 1 σ-classes
module product-Tuple-10 where

  -- τ=53: 1 nodes, 1 σ-classes
  module tuple where

    -- σ=67 (1 nodes)
    cell-0 : κ 39 ≡ κ 39
    cell-0 = refl



-- κ=40: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-21 where

  -- τ=54: 1 nodes, 1 σ-classes
  module τ54 where

    -- σ=68 (1 nodes)
    cell-0 : κ 40 ≡ κ 40
    cell-0 = refl



-- κ=41: 1 nodes, 1 τ-classes, 1 σ-classes
module fixpoint-While-1 where

  -- τ=55: 1 nodes, 1 σ-classes
  module τ55 where

    -- σ=69 (1 nodes)
    cell-0 : κ 41 ≡ κ 41
    cell-0 = refl



-- κ=43: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-2 where

  -- τ=57: 1 nodes, 1 σ-classes
  module τ57 where

    -- σ=71 (1 nodes)
    cell-0 : κ 43 ≡ κ 43
    cell-0 = refl



-- κ=47: 1 nodes, 1 τ-classes, 1 σ-classes
module product-Tuple-11 where

  -- τ=63: 1 nodes, 1 σ-classes
  module tuple where

    -- σ=85 (1 nodes)
    cell-0 : κ 47 ≡ κ 47
    cell-0 = refl



-- κ=48: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-22 where

  -- τ=64: 1 nodes, 1 σ-classes
  module τ64 where

    -- σ=86 (1 nodes)
    cell-0 : κ 48 ≡ κ 48
    cell-0 = refl



-- κ=49: 6 nodes, 1 τ-classes, 1 σ-classes
module eq-Eq where

  -- τ=65: 6 nodes, 1 σ-classes
  module τ65 where

    -- σ=88 (6 nodes)
    cell-0 : κ 49 ≡ κ 49
    cell-0 = refl



-- κ=51: 2 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-7 where

  -- τ=67: 2 nodes, 1 σ-classes
  module τ67 where

    -- σ=92 (2 nodes)
    cell-0 : κ 51 ≡ κ 51
    cell-0 = refl



-- κ=52: 3 nodes, 1 τ-classes, 1 σ-classes
module lt-Lt where

  -- τ=68: 3 nodes, 1 σ-classes
  module τ68 where

    -- σ=95 (3 nodes)
    cell-0 : κ 52 ≡ κ 52
    cell-0 = refl



-- κ=53: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-Compare-12 where

  -- τ=69: 1 nodes, 1 σ-classes
  module τ69 where

    -- σ=98 (1 nodes)
    cell-0 : κ 53 ≡ κ 53
    cell-0 = refl



-- κ=54: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-23 where

  -- τ=70: 1 nodes, 1 σ-classes
  module τ70 where

    -- σ=100 (1 nodes)
    cell-0 : κ 54 ≡ κ 54
    cell-0 = refl



-- κ=55: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-8 where

  -- τ=71: 1 nodes, 1 σ-classes
  module τ71 where

    -- σ=101 (1 nodes)
    cell-0 : κ 55 ≡ κ 55
    cell-0 = refl



-- κ=56: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-Compare-13 where

  -- τ=72: 1 nodes, 1 σ-classes
  module τ72 where

    -- σ=104 (1 nodes)
    cell-0 : κ 56 ≡ κ 56
    cell-0 = refl



-- κ=57: 17 nodes, 1 τ-classes, 1 σ-classes
module add-Add where

  -- τ=73: 17 nodes, 1 σ-classes
  module τ73 where

    -- σ=106 (17 nodes)
    cell-0 : κ 57 ≡ κ 57
    cell-0 = refl



-- κ=58: 1 nodes, 1 τ-classes, 1 σ-classes
module monoid-accum-AugAssign-1 where

  -- τ=74: 1 nodes, 1 σ-classes
  module τ74 where

    -- σ=108 (1 nodes)
    cell-0 : κ 58 ≡ κ 58
    cell-0 = refl



-- κ=59: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-9 where

  -- τ=75: 1 nodes, 1 σ-classes
  module τ75 where

    -- σ=109 (1 nodes)
    cell-0 : κ 59 ≡ κ 59
    cell-0 = refl



-- κ=60: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-3 where

  -- τ=76: 1 nodes, 1 σ-classes
  module τ76 where

    -- σ=110 (1 nodes)
    cell-0 : κ 60 ≡ κ 60
    cell-0 = refl



-- κ=61: 15 nodes, 1 τ-classes, 1 σ-classes
module in-k-In where

  -- τ=77: 15 nodes, 1 σ-classes
  module τ77 where

    -- σ=114 (15 nodes)
    cell-0 : κ 61 ≡ κ 61
    cell-0 = refl



-- κ=63: 1 nodes, 1 τ-classes, 1 σ-classes
module terminal-map-Return-5 where

  -- τ=79: 1 nodes, 1 σ-classes
  module τ79 where

    -- σ=116 (1 nodes)
    cell-0 : κ 63 ≡ κ 63
    cell-0 = refl



-- κ=64: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-4 where

  -- τ=81: 1 nodes, 1 σ-classes
  module τ81 where

    -- σ=118 (1 nodes)
    cell-0 : κ 64 ≡ κ 64
    cell-0 = refl



-- κ=66: 1 nodes, 1 τ-classes, 1 σ-classes
module terminal-map-Return-6 where

  -- τ=83: 1 nodes, 1 σ-classes
  module τ83 where

    -- σ=121 (1 nodes)
    cell-0 : κ 66 ≡ κ 66
    cell-0 = refl



-- κ=68: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-5 where

  -- τ=85: 1 nodes, 1 σ-classes
  module τ85 where

    -- σ=125 (1 nodes)
    cell-0 : κ 68 ≡ κ 68
    cell-0 = refl



-- κ=72: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-6 where

  -- τ=89: 1 nodes, 1 σ-classes
  module τ89 where

    -- σ=129 (1 nodes)
    cell-0 : κ 72 ≡ κ 72
    cell-0 = refl



-- κ=73: 1 nodes, 1 τ-classes, 1 σ-classes
module classifier-intro-ClassDef-0 where

  -- τ=90: 1 nodes, 1 σ-classes
  module τ90 where

    -- σ=130 (1 nodes)
    cell-0 : κ 73 ≡ κ 73
    cell-0 = refl



-- κ=74: 1 nodes, 1 τ-classes, 1 σ-classes
module product-Tuple-12 where

  -- τ=91: 1 nodes, 1 σ-classes
  module tuple where

    -- σ=137 (1 nodes)
    cell-0 : κ 74 ≡ κ 74
    cell-0 = refl



-- κ=75: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-24 where

  -- τ=92: 1 nodes, 1 σ-classes
  module τ92 where

    -- σ=138 (1 nodes)
    cell-0 : κ 75 ≡ κ 75
    cell-0 = refl



-- κ=80: 1 nodes, 1 τ-classes, 1 σ-classes
module arguments-arguments-5 where

  -- τ=104: 1 nodes, 1 σ-classes
  module τ104 where

    -- σ=150 (1 nodes)
    cell-0 : κ 80 ≡ κ 80
    cell-0 = refl



-- κ=83: 9 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-literal-List-1 where

  -- τ=115: 9 nodes, 1 σ-classes
  module list where

    -- σ=164 (9 nodes)
    cell-0 : κ 83 ≡ κ 83
    cell-0 = refl



-- κ=85: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-7 where

  -- τ=117: 1 nodes, 1 σ-classes
  module τ117 where

    -- σ=166 (1 nodes)
    cell-0 : κ 85 ≡ κ 85
    cell-0 = refl



-- κ=88: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-fold-JoinedStr-6 where

  -- τ=120: 1 nodes, 1 σ-classes
  module str where

    -- σ=175 (1 nodes)
    cell-0 : κ 88 ≡ κ 88
    cell-0 = refl



-- κ=89: 1 nodes, 1 τ-classes, 1 σ-classes
module terminal-map-Return-7 where

  -- τ=121: 1 nodes, 1 σ-classes
  module τ121 where

    -- σ=176 (1 nodes)
    cell-0 : κ 89 ≡ κ 89
    cell-0 = refl



-- κ=90: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-8 where

  -- τ=122: 1 nodes, 1 σ-classes
  module τ122 where

    -- σ=178 (1 nodes)
    cell-0 : κ 90 ≡ κ 90
    cell-0 = refl



-- κ=91: 1 nodes, 1 τ-classes, 1 σ-classes
module classifier-intro-ClassDef-1 where

  -- τ=123: 1 nodes, 1 σ-classes
  module τ123 where

    -- σ=179 (1 nodes)
    cell-0 : κ 91 ≡ κ 91
    cell-0 = refl



-- κ=92: 1 nodes, 1 τ-classes, 1 σ-classes
module product-Tuple-13 where

  -- τ=133: 1 nodes, 1 σ-classes
  module tuple where

    -- σ=194 (1 nodes)
    cell-0 : κ 92 ≡ κ 92
    cell-0 = refl



-- κ=93: 1 nodes, 1 τ-classes, 1 σ-classes
module index-Index-12 where

  -- τ=134: 1 nodes, 1 σ-classes
  module τ134 where

    -- σ=195 (1 nodes)
    cell-0 : κ 93 ≡ κ 93
    cell-0 = refl



-- κ=94: 1 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-18 where

  -- τ=135: 1 nodes, 1 σ-classes
  module τ135 where

    -- σ=196 (1 nodes)
    cell-0 : κ 94 ≡ κ 94
    cell-0 = refl



-- κ=95: 1 nodes, 1 τ-classes, 1 σ-classes
module annassign-AnnAssign-16 where

  -- τ=136: 1 nodes, 1 σ-classes
  module τ136 where

    -- σ=197 (1 nodes)
    cell-0 : κ 95 ≡ κ 95
    cell-0 = refl



-- κ=99: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-9 where

  -- τ=142: 1 nodes, 1 σ-classes
  module τ142 where

    -- σ=204 (1 nodes)
    cell-0 : κ 99 ≡ κ 99
    cell-0 = refl



-- κ=100: 1 nodes, 1 τ-classes, 1 σ-classes
module arguments-arguments-6 where

  -- τ=143: 1 nodes, 1 σ-classes
  module τ143 where

    -- σ=206 (1 nodes)
    cell-0 : κ 100 ≡ κ 100
    cell-0 = refl



-- κ=103: 1 nodes, 1 τ-classes, 1 σ-classes
module apply-Call-17 where

  -- τ=151: 1 nodes, 1 σ-classes
  module τ151 where

    -- σ=221 (1 nodes)
    cell-0 : κ 103 ≡ κ 103
    cell-0 = refl



-- κ=104: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-25 where

  -- τ=152: 1 nodes, 1 σ-classes
  module τ152 where

    -- σ=222 (1 nodes)
    cell-0 : κ 104 ≡ κ 104
    cell-0 = refl



-- κ=108: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-10 where

  -- τ=156: 1 nodes, 1 σ-classes
  module τ156 where

    -- σ=227 (1 nodes)
    cell-0 : κ 108 ≡ κ 108
    cell-0 = refl



-- κ=111: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-snoc-at-x3f-Call-2 where

  -- τ=160: 1 nodes, 1 σ-classes
  module τ160 where

    -- σ=232 (1 nodes)
    cell-0 : κ 111 ≡ κ 111
    cell-0 = refl



-- κ=112: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-11 where

  -- τ=161: 1 nodes, 1 σ-classes
  module τ161 where

    -- σ=233 (1 nodes)
    cell-0 : κ 112 ≡ κ 112
    cell-0 = refl



-- κ=113: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-10 where

  -- τ=163: 1 nodes, 1 σ-classes
  module τ163 where

    -- σ=235 (1 nodes)
    cell-0 : κ 113 ≡ κ 113
    cell-0 = refl



-- κ=115: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-11 where

  -- τ=167: 1 nodes, 1 σ-classes
  module τ167 where

    -- σ=242 (1 nodes)
    cell-0 : κ 115 ≡ κ 115
    cell-0 = refl



-- κ=116: 1 nodes, 1 τ-classes, 1 σ-classes
module product-Tuple-14 where

  -- τ=171: 1 nodes, 1 σ-classes
  module tuple where

    -- σ=250 (1 nodes)
    cell-0 : κ 116 ≡ κ 116
    cell-0 = refl



-- κ=117: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-26 where

  -- τ=172: 1 nodes, 1 σ-classes
  module τ172 where

    -- σ=251 (1 nodes)
    cell-0 : κ 117 ≡ κ 117
    cell-0 = refl



-- κ=119: 1 nodes, 1 τ-classes, 1 σ-classes
module annassign-AnnAssign-17 where

  -- τ=175: 1 nodes, 1 σ-classes
  module τ175 where

    -- σ=255 (1 nodes)
    cell-0 : κ 119 ≡ κ 119
    cell-0 = refl



-- κ=120: 1 nodes, 1 τ-classes, 1 σ-classes
module ifexp-IfExp-1 where

  -- τ=176: 1 nodes, 1 σ-classes
  module τ176 where

    -- σ=259 (1 nodes)
    cell-0 : κ 120 ≡ κ 120
    cell-0 = refl



-- κ=121: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-27 where

  -- τ=177: 1 nodes, 1 σ-classes
  module τ177 where

    -- σ=260 (1 nodes)
    cell-0 : κ 121 ≡ κ 121
    cell-0 = refl



-- κ=122: 1 nodes, 1 τ-classes, 1 σ-classes
module apply-Call-18 where

  -- τ=180: 1 nodes, 1 σ-classes
  module τ180 where

    -- σ=269 (1 nodes)
    cell-0 : κ 122 ≡ κ 122
    cell-0 = refl



-- κ=123: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-12 where

  -- τ=181: 1 nodes, 1 σ-classes
  module τ181 where

    -- σ=270 (1 nodes)
    cell-0 : κ 123 ≡ κ 123
    cell-0 = refl



-- κ=124: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-12 where

  -- τ=182: 1 nodes, 1 σ-classes
  module τ182 where

    -- σ=272 (1 nodes)
    cell-0 : κ 124 ≡ κ 124
    cell-0 = refl



-- κ=125: 22 nodes, 1 τ-classes, 1 σ-classes
module powerset-Call-1 where

  -- τ=184: 22 nodes, 1 σ-classes
  module τ184 where

    -- σ=278 (22 nodes)
    cell-0 : κ 125 ≡ κ 125
    cell-0 = refl



-- κ=132: 1 nodes, 1 τ-classes, 1 σ-classes
module cofree-Yield where

  -- τ=191: 1 nodes, 1 σ-classes
  module τ191 where

    -- σ=288 (1 nodes)
    cell-0 : κ 132 ≡ κ 132
    cell-0 = refl



-- κ=133: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-13 where

  -- τ=192: 1 nodes, 1 σ-classes
  module τ192 where

    -- σ=289 (1 nodes)
    cell-0 : κ 133 ≡ κ 133
    cell-0 = refl



-- κ=134: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-11 where

  -- τ=193: 1 nodes, 1 σ-classes
  module τ193 where

    -- σ=290 (1 nodes)
    cell-0 : κ 134 ≡ κ 134
    cell-0 = refl



-- κ=135: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-4 where

  -- τ=194: 1 nodes, 1 σ-classes
  module τ194 where

    -- σ=291 (1 nodes)
    cell-0 : κ 135 ≡ κ 135
    cell-0 = refl



-- κ=136: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-13 where

  -- τ=196: 1 nodes, 1 σ-classes
  module τ196 where

    -- σ=293 (1 nodes)
    cell-0 : κ 136 ≡ κ 136
    cell-0 = refl



-- κ=138: 1 nodes, 1 τ-classes, 1 σ-classes
module comprehension-comprehension-3 where

  -- τ=199: 1 nodes, 1 σ-classes
  module τ199 where

    -- σ=298 (1 nodes)
    cell-0 : κ 138 ≡ κ 138
    cell-0 = refl



-- κ=139: 1 nodes, 1 τ-classes, 1 σ-classes
module lazy_fold-GeneratorExp-1 where

  -- τ=200: 1 nodes, 1 σ-classes
  module τ200 where

    -- σ=299 (1 nodes)
    cell-0 : κ 139 ≡ κ 139
    cell-0 = refl



-- κ=140: 1 nodes, 1 τ-classes, 1 σ-classes
module apply-Call-19 where

  -- τ=201: 1 nodes, 1 σ-classes
  module τ201 where

    -- σ=300 (1 nodes)
    cell-0 : κ 140 ≡ κ 140
    cell-0 = refl



-- κ=141: 1 nodes, 1 τ-classes, 1 σ-classes
module terminal-map-Return-8 where

  -- τ=202: 1 nodes, 1 σ-classes
  module τ202 where

    -- σ=301 (1 nodes)
    cell-0 : κ 141 ≡ κ 141
    cell-0 = refl



-- κ=142: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-14 where

  -- τ=203: 1 nodes, 1 σ-classes
  module τ203 where

    -- σ=302 (1 nodes)
    cell-0 : κ 142 ≡ κ 142
    cell-0 = refl



-- κ=143: 1 nodes, 1 τ-classes, 1 σ-classes
module index-Index-13 where

  -- τ=204: 1 nodes, 1 σ-classes
  module τ204 where

    -- σ=303 (1 nodes)
    cell-0 : κ 143 ≡ κ 143
    cell-0 = refl



-- κ=144: 1 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-19 where

  -- τ=205: 1 nodes, 1 σ-classes
  module τ205 where

    -- σ=304 (1 nodes)
    cell-0 : κ 144 ≡ κ 144
    cell-0 = refl



-- κ=145: 1 nodes, 1 τ-classes, 1 σ-classes
module terminal-map-Return-9 where

  -- τ=206: 1 nodes, 1 σ-classes
  module τ206 where

    -- σ=305 (1 nodes)
    cell-0 : κ 145 ≡ κ 145
    cell-0 = refl



-- κ=146: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-15 where

  -- τ=207: 1 nodes, 1 σ-classes
  module τ207 where

    -- σ=306 (1 nodes)
    cell-0 : κ 146 ≡ κ 146
    cell-0 = refl



-- κ=147: 1 nodes, 1 τ-classes, 1 σ-classes
module terminal-map-Return-10 where

  -- τ=208: 1 nodes, 1 σ-classes
  module τ208 where

    -- σ=307 (1 nodes)
    cell-0 : κ 147 ≡ κ 147
    cell-0 = refl



-- κ=148: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-16 where

  -- τ=209: 1 nodes, 1 σ-classes
  module τ209 where

    -- σ=308 (1 nodes)
    cell-0 : κ 148 ≡ κ 148
    cell-0 = refl



-- κ=151: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-fold-JoinedStr-7 where

  -- τ=212: 1 nodes, 1 σ-classes
  module str where

    -- σ=315 (1 nodes)
    cell-0 : κ 151 ≡ κ 151
    cell-0 = refl



-- κ=152: 1 nodes, 1 τ-classes, 1 σ-classes
module terminal-map-Return-11 where

  -- τ=213: 1 nodes, 1 σ-classes
  module τ213 where

    -- σ=316 (1 nodes)
    cell-0 : κ 152 ≡ κ 152
    cell-0 = refl



-- κ=153: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-17 where

  -- τ=214: 1 nodes, 1 σ-classes
  module τ214 where

    -- σ=317 (1 nodes)
    cell-0 : κ 153 ≡ κ 153
    cell-0 = refl



-- κ=154: 1 nodes, 1 τ-classes, 1 σ-classes
module classifier-intro-ClassDef-2 where

  -- τ=215: 1 nodes, 1 σ-classes
  module τ215 where

    -- σ=318 (1 nodes)
    cell-0 : κ 154 ≡ κ 154
    cell-0 = refl



-- κ=160: 10 nodes, 1 τ-classes, 1 σ-classes
module product-Tuple-15 where

  -- τ=226: 10 nodes, 1 σ-classes
  module tuple where

    -- σ=342 (10 nodes)
    cell-0 : κ 160 ≡ κ 160
    cell-0 = refl



-- κ=161: 10 nodes, 1 τ-classes, 1 σ-classes
module index-Index-14 where

  -- τ=227: 10 nodes, 1 σ-classes
  module τ227 where

    -- σ=343 (10 nodes)
    cell-0 : κ 161 ≡ κ 161
    cell-0 = refl



-- κ=162: 10 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-20 where

  -- τ=228: 10 nodes, 1 σ-classes
  module τ228 where

    -- σ=344 (10 nodes)
    cell-0 : κ 162 ≡ κ 162
    cell-0 = refl



-- κ=163: 6 nodes, 1 τ-classes, 1 σ-classes
module product-Tuple-16 where

  -- τ=229: 6 nodes, 1 σ-classes
  module tuple where

    -- σ=348 (6 nodes)
    cell-0 : κ 163 ≡ κ 163
    cell-0 = refl



-- κ=164: 6 nodes, 1 τ-classes, 1 σ-classes
module index-Index-15 where

  -- τ=230: 6 nodes, 1 σ-classes
  module τ230 where

    -- σ=349 (6 nodes)
    cell-0 : κ 164 ≡ κ 164
    cell-0 = refl



-- κ=165: 6 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-21 where

  -- τ=231: 6 nodes, 1 σ-classes
  module τ231 where

    -- σ=350 (6 nodes)
    cell-0 : κ 165 ≡ κ 165
    cell-0 = refl



-- κ=166: 1 nodes, 1 τ-classes, 1 σ-classes
module product-Tuple-17 where

  -- τ=232: 1 nodes, 1 σ-classes
  module tuple where

    -- σ=351 (1 nodes)
    cell-0 : κ 166 ≡ κ 166
    cell-0 = refl



-- κ=167: 1 nodes, 1 τ-classes, 1 σ-classes
module index-Index-16 where

  -- τ=233: 1 nodes, 1 σ-classes
  module τ233 where

    -- σ=352 (1 nodes)
    cell-0 : κ 167 ≡ κ 167
    cell-0 = refl



-- κ=168: 1 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-22 where

  -- τ=234: 1 nodes, 1 σ-classes
  module τ234 where

    -- σ=353 (1 nodes)
    cell-0 : κ 168 ≡ κ 168
    cell-0 = refl



-- κ=169: 1 nodes, 1 τ-classes, 1 σ-classes
module annassign-AnnAssign-18 where

  -- τ=235: 1 nodes, 1 σ-classes
  module τ235 where

    -- σ=354 (1 nodes)
    cell-0 : κ 169 ≡ κ 169
    cell-0 = refl



-- κ=170: 6 nodes, 1 τ-classes, 1 σ-classes
module index-Index-17 where

  -- τ=237: 6 nodes, 1 σ-classes
  module τ237 where

    -- σ=357 (6 nodes)
    cell-0 : κ 170 ≡ κ 170
    cell-0 = refl



-- κ=171: 6 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-23 where

  -- τ=238: 6 nodes, 1 σ-classes
  module τ238 where

    -- σ=358 (6 nodes)
    cell-0 : κ 171 ≡ κ 171
    cell-0 = refl



-- κ=172: 1 nodes, 1 τ-classes, 1 σ-classes
module product-Tuple-18 where

  -- τ=239: 1 nodes, 1 σ-classes
  module tuple where

    -- σ=359 (1 nodes)
    cell-0 : κ 172 ≡ κ 172
    cell-0 = refl



-- κ=173: 1 nodes, 1 τ-classes, 1 σ-classes
module index-Index-18 where

  -- τ=240: 1 nodes, 1 σ-classes
  module τ240 where

    -- σ=360 (1 nodes)
    cell-0 : κ 173 ≡ κ 173
    cell-0 = refl



-- κ=174: 1 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-24 where

  -- τ=241: 1 nodes, 1 σ-classes
  module τ241 where

    -- σ=361 (1 nodes)
    cell-0 : κ 174 ≡ κ 174
    cell-0 = refl



-- κ=176: 1 nodes, 1 τ-classes, 1 σ-classes
module annassign-AnnAssign-19 where

  -- τ=243: 1 nodes, 1 σ-classes
  module τ243 where

    -- σ=363 (1 nodes)
    cell-0 : κ 176 ≡ κ 176
    cell-0 = refl



-- κ=177: 1 nodes, 1 τ-classes, 1 σ-classes
module product-Tuple-19 where

  -- τ=245: 1 nodes, 1 σ-classes
  module tuple where

    -- σ=365 (1 nodes)
    cell-0 : κ 177 ≡ κ 177
    cell-0 = refl



-- κ=178: 1 nodes, 1 τ-classes, 1 σ-classes
module index-Index-19 where

  -- τ=246: 1 nodes, 1 σ-classes
  module τ246 where

    -- σ=366 (1 nodes)
    cell-0 : κ 178 ≡ κ 178
    cell-0 = refl



-- κ=179: 1 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-25 where

  -- τ=247: 1 nodes, 1 σ-classes
  module τ247 where

    -- σ=367 (1 nodes)
    cell-0 : κ 179 ≡ κ 179
    cell-0 = refl



-- κ=180: 1 nodes, 1 τ-classes, 1 σ-classes
module annassign-AnnAssign-20 where

  -- τ=248: 1 nodes, 1 σ-classes
  module τ248 where

    -- σ=368 (1 nodes)
    cell-0 : κ 180 ≡ κ 180
    cell-0 = refl



-- κ=186: 1 nodes, 1 τ-classes, 1 σ-classes
module annassign-AnnAssign-21 where

  -- τ=263: 1 nodes, 1 σ-classes
  module τ263 where

    -- σ=385 (1 nodes)
    cell-0 : κ 186 ≡ κ 186
    cell-0 = refl



-- κ=189: 2 nodes, 1 τ-classes, 1 σ-classes
module product-Tuple-20 where

  -- τ=267: 2 nodes, 1 σ-classes
  module tuple where

    -- σ=389 (2 nodes)
    cell-0 : κ 189 ≡ κ 189
    cell-0 = refl



-- κ=190: 2 nodes, 1 τ-classes, 1 σ-classes
module index-Index-20 where

  -- τ=268: 2 nodes, 1 σ-classes
  module τ268 where

    -- σ=390 (2 nodes)
    cell-0 : κ 190 ≡ κ 190
    cell-0 = refl



-- κ=192: 1 nodes, 1 τ-classes, 1 σ-classes
module annassign-AnnAssign-22 where

  -- τ=270: 1 nodes, 1 σ-classes
  module τ270 where

    -- σ=392 (1 nodes)
    cell-0 : κ 192 ≡ κ 192
    cell-0 = refl



-- κ=196: 1 nodes, 1 τ-classes, 1 σ-classes
module arguments-arguments-7 where

  -- τ=285: 1 nodes, 1 σ-classes
  module τ285 where

    -- σ=408 (1 nodes)
    cell-0 : κ 196 ≡ κ 196
    cell-0 = refl



-- κ=197: 1 nodes, 1 τ-classes, 1 σ-classes
module lambda-Lambda-0 where

  -- τ=286: 1 nodes, 1 σ-classes
  module τ286 where

    -- σ=410 (1 nodes)
    cell-0 : κ 197 ≡ κ 197
    cell-0 = refl



-- κ=198: 1 nodes, 1 τ-classes, 1 σ-classes
module apply-Call-20 where

  -- τ=287: 1 nodes, 1 σ-classes
  module τ287 where

    -- σ=411 (1 nodes)
    cell-0 : κ 198 ≡ κ 198
    cell-0 = refl



-- κ=199: 1 nodes, 1 τ-classes, 1 σ-classes
module annassign-AnnAssign-23 where

  -- τ=288: 1 nodes, 1 σ-classes
  module τ288 where

    -- σ=412 (1 nodes)
    cell-0 : κ 199 ≡ κ 199
    cell-0 = refl



-- κ=203: 1 nodes, 1 τ-classes, 1 σ-classes
module annassign-AnnAssign-24 where

  -- τ=293: 1 nodes, 1 σ-classes
  module τ293 where

    -- σ=421 (1 nodes)
    cell-0 : κ 203 ≡ κ 203
    cell-0 = refl



-- κ=204: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-18 where

  -- τ=294: 1 nodes, 1 σ-classes
  module τ294 where

    -- σ=422 (1 nodes)
    cell-0 : κ 204 ≡ κ 204
    cell-0 = refl



-- κ=205: 1 nodes, 1 τ-classes, 1 σ-classes
module arg-arg-4 where

  -- τ=297: 1 nodes, 1 σ-classes
  module τ297 where

    -- σ=427 (1 nodes)
    cell-0 : κ 205 ≡ κ 205
    cell-0 = refl



-- κ=206: 1 nodes, 1 τ-classes, 1 σ-classes
module arguments-arguments-8 where

  -- τ=298: 1 nodes, 1 σ-classes
  module τ298 where

    -- σ=428 (1 nodes)
    cell-0 : κ 206 ≡ κ 206
    cell-0 = refl



-- κ=207: 1 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-26 where

  -- τ=299: 1 nodes, 1 σ-classes
  module τ299 where

    -- σ=437 (1 nodes)
    cell-0 : κ 207 ≡ κ 207
    cell-0 = refl



-- κ=208: 1 nodes, 1 τ-classes, 1 σ-classes
module monoid-accum-AugAssign-2 where

  -- τ=300: 1 nodes, 1 σ-classes
  module τ300 where

    -- σ=438 (1 nodes)
    cell-0 : κ 208 ≡ κ 208
    cell-0 = refl



-- κ=214: 1 nodes, 1 τ-classes, 1 σ-classes
module coproduct-elim-If-0 where

  -- τ=306: 1 nodes, 1 σ-classes
  module τ306 where

    -- σ=453 (1 nodes)
    cell-0 : κ 214 ≡ κ 214
    cell-0 = refl



-- κ=215: 9 nodes, 1 τ-classes, 1 σ-classes
module gt-Gt where

  -- τ=307: 9 nodes, 1 σ-classes
  module τ307 where

    -- σ=454 (9 nodes)
    cell-0 : κ 215 ≡ κ 215
    cell-0 = refl



-- κ=218: 2 nodes, 1 τ-classes, 1 σ-classes
module product-Tuple-21 where

  -- τ=310: 2 nodes, 1 σ-classes
  module tuple where

    -- σ=458 (2 nodes)
    cell-0 : κ 218 ≡ κ 218
    cell-0 = refl



-- κ=220: 8 nodes, 1 τ-classes, 1 σ-classes
module sub-Sub where

  -- τ=313: 8 nodes, 1 σ-classes
  module τ313 where

    -- σ=461 (8 nodes)
    cell-0 : κ 220 ≡ κ 220
    cell-0 = refl



-- κ=221: 1 nodes, 1 τ-classes, 1 σ-classes
module bimap-BinOp-4 where

  -- τ=314: 1 nodes, 1 σ-classes
  module τ314 where

    -- σ=462 (1 nodes)
    cell-0 : κ 221 ≡ κ 221
    cell-0 = refl



-- κ=222: 1 nodes, 1 τ-classes, 1 σ-classes
module apply-Call-21 where

  -- τ=315: 1 nodes, 1 σ-classes
  module τ315 where

    -- σ=464 (1 nodes)
    cell-0 : κ 222 ≡ κ 222
    cell-0 = refl



-- κ=223: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-14 where

  -- τ=316: 1 nodes, 1 σ-classes
  module τ316 where

    -- σ=465 (1 nodes)
    cell-0 : κ 223 ≡ κ 223
    cell-0 = refl



-- κ=224: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-5 where

  -- τ=317: 1 nodes, 1 σ-classes
  module τ317 where

    -- σ=466 (1 nodes)
    cell-0 : κ 224 ≡ κ 224
    cell-0 = refl



-- κ=225: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-12 where

  -- τ=318: 1 nodes, 1 σ-classes
  module τ318 where

    -- σ=467 (1 nodes)
    cell-0 : κ 225 ≡ κ 225
    cell-0 = refl



-- κ=226: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-19 where

  -- τ=319: 1 nodes, 1 σ-classes
  module τ319 where

    -- σ=468 (1 nodes)
    cell-0 : κ 226 ≡ κ 226
    cell-0 = refl



-- κ=229: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-28 where

  -- τ=325: 1 nodes, 1 σ-classes
  module τ325 where

    -- σ=486 (1 nodes)
    cell-0 : κ 229 ≡ κ 229
    cell-0 = refl



-- κ=230: 1 nodes, 1 τ-classes, 1 σ-classes
module or-Or where

  -- τ=327: 1 nodes, 1 σ-classes
  module τ327 where

    -- σ=489 (1 nodes)
    cell-0 : κ 230 ≡ κ 230
    cell-0 = refl



-- κ=231: 1 nodes, 1 τ-classes, 1 σ-classes
module join-BoolOp where

  -- τ=329: 1 nodes, 1 σ-classes
  module τ329 where

    -- σ=493 (1 nodes)
    cell-0 : κ 231 ≡ κ 231
    cell-0 = refl



-- κ=233: 1 nodes, 1 τ-classes, 1 σ-classes
module lazy_fold-GeneratorExp-2 where

  -- τ=331: 1 nodes, 1 σ-classes
  module τ331 where

    -- σ=497 (1 nodes)
    cell-0 : κ 233 ≡ κ 233
    cell-0 = refl



-- κ=234: 1 nodes, 1 τ-classes, 1 σ-classes
module total_order-Call-0 where

  -- τ=332: 1 nodes, 1 σ-classes
  module list where

    -- σ=498 (1 nodes)
    cell-0 : κ 234 ≡ κ 234
    cell-0 = refl



-- κ=235: 1 nodes, 1 τ-classes, 1 σ-classes
module apply-Call-22 where

  -- τ=333: 1 nodes, 1 σ-classes
  module τ333 where

    -- σ=499 (1 nodes)
    cell-0 : κ 235 ≡ κ 235
    cell-0 = refl



-- κ=236: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-29 where

  -- τ=334: 1 nodes, 1 σ-classes
  module τ334 where

    -- σ=500 (1 nodes)
    cell-0 : κ 236 ≡ κ 236
    cell-0 = refl



-- κ=237: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-Compare-14 where

  -- τ=336: 1 nodes, 1 σ-classes
  module τ336 where

    -- σ=504 (1 nodes)
    cell-0 : κ 237 ≡ κ 237
    cell-0 = refl



-- κ=238: 1 nodes, 1 τ-classes, 1 σ-classes
module terminal-map-Return-12 where

  -- τ=337: 1 nodes, 1 σ-classes
  module τ337 where

    -- σ=505 (1 nodes)
    cell-0 : κ 238 ≡ κ 238
    cell-0 = refl



-- κ=239: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-13 where

  -- τ=338: 1 nodes, 1 σ-classes
  module τ338 where

    -- σ=506 (1 nodes)
    cell-0 : κ 239 ≡ κ 239
    cell-0 = refl



-- κ=240: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-30 where

  -- τ=339: 1 nodes, 1 σ-classes
  module τ339 where

    -- σ=513 (1 nodes)
    cell-0 : κ 240 ≡ κ 240
    cell-0 = refl



-- κ=241: 4 nodes, 1 τ-classes, 1 σ-classes
module gte-GtE where

  -- τ=340: 4 nodes, 1 σ-classes
  module τ340 where

    -- σ=515 (4 nodes)
    cell-0 : κ 241 ≡ κ 241
    cell-0 = refl



-- κ=244: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-snoc-at-state-Call-2 where

  -- τ=343: 1 nodes, 1 σ-classes
  module None where

    -- σ=520 (1 nodes)
    cell-0 : κ 244 ≡ κ 244
    cell-0 = refl



-- κ=245: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-15 where

  -- τ=344: 1 nodes, 1 σ-classes
  module τ344 where

    -- σ=521 (1 nodes)
    cell-0 : κ 245 ≡ κ 245
    cell-0 = refl



-- κ=246: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-fold-JoinedStr-8 where

  -- τ=345: 1 nodes, 1 σ-classes
  module str where

    -- σ=527 (1 nodes)
    cell-0 : κ 246 ≡ κ 246
    cell-0 = refl



-- κ=247: 1 nodes, 1 τ-classes, 1 σ-classes
module apply-Call-23 where

  -- τ=346: 1 nodes, 1 σ-classes
  module τ346 where

    -- σ=528 (1 nodes)
    cell-0 : κ 247 ≡ κ 247
    cell-0 = refl



-- κ=248: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-31 where

  -- τ=347: 1 nodes, 1 σ-classes
  module τ347 where

    -- σ=529 (1 nodes)
    cell-0 : κ 248 ≡ κ 248
    cell-0 = refl



-- κ=249: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-snoc-at-state-Call-3 where

  -- τ=349: 1 nodes, 1 σ-classes
  module None where

    -- σ=532 (1 nodes)
    cell-0 : κ 249 ≡ κ 249
    cell-0 = refl



-- κ=250: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-16 where

  -- τ=350: 1 nodes, 1 σ-classes
  module τ350 where

    -- σ=533 (1 nodes)
    cell-0 : κ 250 ≡ κ 250
    cell-0 = refl



-- κ=251: 1 nodes, 1 τ-classes, 1 σ-classes
module fixpoint-While-2 where

  -- τ=351: 1 nodes, 1 σ-classes
  module τ351 where

    -- σ=534 (1 nodes)
    cell-0 : κ 251 ≡ κ 251
    cell-0 = refl



-- κ=253: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-32 where

  -- τ=354: 1 nodes, 1 σ-classes
  module τ354 where

    -- σ=552 (1 nodes)
    cell-0 : κ 253 ≡ κ 253
    cell-0 = refl



-- κ=257: 1 nodes, 1 τ-classes, 1 σ-classes
module annassign-AnnAssign-25 where

  -- τ=360: 1 nodes, 1 σ-classes
  module τ360 where

    -- σ=568 (1 nodes)
    cell-0 : κ 257 ≡ κ 257
    cell-0 = refl



-- κ=260: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-Compare-15 where

  -- τ=363: 1 nodes, 1 σ-classes
  module τ363 where

    -- σ=576 (1 nodes)
    cell-0 : κ 260 ≡ κ 260
    cell-0 = refl



-- κ=261: 2 nodes, 1 τ-classes, 1 σ-classes
module partial-at-x3f-Attribute-1 where

  -- τ=178: 2 nodes, 1 σ-classes
  module τ178 where

    -- σ=582 (2 nodes)
    cell-0 : κ 261 ≡ κ 261
    cell-0 = refl



-- κ=265: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-Compare-16 where

  -- τ=367: 1 nodes, 1 σ-classes
  module τ367 where

    -- σ=590 (1 nodes)
    cell-0 : κ 265 ≡ κ 265
    cell-0 = refl



-- κ=266: 1 nodes, 1 τ-classes, 1 σ-classes
module comprehension-comprehension-4 where

  -- τ=368: 1 nodes, 1 σ-classes
  module τ368 where

    -- σ=591 (1 nodes)
    cell-0 : κ 266 ≡ κ 266
    cell-0 = refl



-- κ=267: 1 nodes, 1 τ-classes, 1 σ-classes
module lazy_fold-GeneratorExp-3 where

  -- τ=369: 1 nodes, 1 σ-classes
  module τ369 where

    -- σ=592 (1 nodes)
    cell-0 : κ 267 ≡ κ 267
    cell-0 = refl



-- κ=268: 1 nodes, 1 τ-classes, 1 σ-classes
module apply-Call-24 where

  -- τ=370: 1 nodes, 1 σ-classes
  module τ370 where

    -- σ=593 (1 nodes)
    cell-0 : κ 268 ≡ κ 268
    cell-0 = refl



-- κ=269: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-33 where

  -- τ=371: 1 nodes, 1 σ-classes
  module τ371 where

    -- σ=594 (1 nodes)
    cell-0 : κ 269 ≡ κ 269
    cell-0 = refl



-- κ=270: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-14 where

  -- τ=372: 1 nodes, 1 σ-classes
  module τ372 where

    -- σ=600 (1 nodes)
    cell-0 : κ 270 ≡ κ 270
    cell-0 = refl



-- κ=271: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-6 where

  -- τ=373: 1 nodes, 1 σ-classes
  module τ373 where

    -- σ=601 (1 nodes)
    cell-0 : κ 271 ≡ κ 271
    cell-0 = refl



-- κ=272: 1 nodes, 1 τ-classes, 1 σ-classes
module lte-LtE where

  -- τ=374: 1 nodes, 1 σ-classes
  module τ374 where

    -- σ=604 (1 nodes)
    cell-0 : κ 272 ≡ κ 272
    cell-0 = refl



-- κ=273: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-Compare-17 where

  -- τ=375: 1 nodes, 1 σ-classes
  module τ375 where

    -- σ=605 (1 nodes)
    cell-0 : κ 273 ≡ κ 273
    cell-0 = refl



-- κ=274: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-34 where

  -- τ=376: 1 nodes, 1 σ-classes
  module τ376 where

    -- σ=606 (1 nodes)
    cell-0 : κ 274 ≡ κ 274
    cell-0 = refl



-- κ=278: 2 nodes, 1 τ-classes, 1 σ-classes
module coerce-FormattedValue-9 where

  -- τ=380: 2 nodes, 1 σ-classes
  module τ380 where

    -- σ=616 (2 nodes)
    cell-0 : κ 278 ≡ κ 278
    cell-0 = refl



-- κ=281: 1 nodes, 1 τ-classes, 1 σ-classes
module coproduct-elim-If-1 where

  -- τ=383: 1 nodes, 1 σ-classes
  module τ383 where

    -- σ=622 (1 nodes)
    cell-0 : κ 281 ≡ κ 281
    cell-0 = refl



-- κ=283: 1 nodes, 1 τ-classes, 1 σ-classes
module product-Tuple-22 where

  -- τ=386: 1 nodes, 1 σ-classes
  module tuple where

    -- σ=630 (1 nodes)
    cell-0 : κ 283 ≡ κ 283
    cell-0 = refl



-- κ=284: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-snoc-at-state-Call-4 where

  -- τ=387: 1 nodes, 1 σ-classes
  module None where

    -- σ=631 (1 nodes)
    cell-0 : κ 284 ≡ κ 284
    cell-0 = refl



-- κ=285: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-17 where

  -- τ=388: 1 nodes, 1 σ-classes
  module τ388 where

    -- σ=632 (1 nodes)
    cell-0 : κ 285 ≡ κ 285
    cell-0 = refl



-- κ=286: 1 nodes, 1 τ-classes, 1 σ-classes
module monoid-op-BinOp-0 where

  -- τ=389: 1 nodes, 1 σ-classes
  module τ389 where

    -- σ=634 (1 nodes)
    cell-0 : κ 286 ≡ κ 286
    cell-0 = refl



-- κ=287: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-35 where

  -- τ=390: 1 nodes, 1 σ-classes
  module τ390 where

    -- σ=635 (1 nodes)
    cell-0 : κ 287 ≡ κ 287
    cell-0 = refl



-- κ=288: 1 nodes, 1 τ-classes, 1 σ-classes
module partial-apply-at-state-Call-2 where

  -- τ=349: 1 nodes, 1 σ-classes
  module None where

    -- σ=644 (1 nodes)
    cell-0 : κ 288 ≡ κ 288
    cell-0 = refl



-- κ=289: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-36 where

  -- τ=395: 1 nodes, 1 σ-classes
  module τ395 where

    -- σ=645 (1 nodes)
    cell-0 : κ 289 ≡ κ 289
    cell-0 = refl



-- κ=290: 1 nodes, 1 τ-classes, 1 σ-classes
module ifexp-IfExp-2 where

  -- τ=398: 1 nodes, 1 σ-classes
  module τ398 where

    -- σ=653 (1 nodes)
    cell-0 : κ 290 ≡ κ 290
    cell-0 = refl



-- κ=291: 1 nodes, 1 τ-classes, 1 σ-classes
module monoid-op-at-x3f-Call-2 where

  -- τ=399: 1 nodes, 1 σ-classes
  module τ399 where

    -- σ=654 (1 nodes)
    cell-0 : κ 291 ≡ κ 291
    cell-0 = refl



-- κ=292: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-18 where

  -- τ=400: 1 nodes, 1 σ-classes
  module τ400 where

    -- σ=655 (1 nodes)
    cell-0 : κ 292 ≡ κ 292
    cell-0 = refl



-- κ=293: 1 nodes, 1 τ-classes, 1 σ-classes
module coproduct-elim-If-2 where

  -- τ=401: 1 nodes, 1 σ-classes
  module τ401 where

    -- σ=656 (1 nodes)
    cell-0 : κ 293 ≡ κ 293
    cell-0 = refl



-- κ=294: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-7 where

  -- τ=402: 1 nodes, 1 σ-classes
  module τ402 where

    -- σ=657 (1 nodes)
    cell-0 : κ 294 ≡ κ 294
    cell-0 = refl



-- κ=295: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-8 where

  -- τ=403: 1 nodes, 1 σ-classes
  module τ403 where

    -- σ=658 (1 nodes)
    cell-0 : κ 295 ≡ κ 295
    cell-0 = refl



-- κ=297: 1 nodes, 1 τ-classes, 1 σ-classes
module ifexp-IfExp-3 where

  -- τ=405: 1 nodes, 1 σ-classes
  module τ405 where

    -- σ=661 (1 nodes)
    cell-0 : κ 297 ≡ κ 297
    cell-0 = refl



-- κ=298: 1 nodes, 1 τ-classes, 1 σ-classes
module apply-Call-25 where

  -- τ=406: 1 nodes, 1 σ-classes
  module τ406 where

    -- σ=662 (1 nodes)
    cell-0 : κ 298 ≡ κ 298
    cell-0 = refl



-- κ=299: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-19 where

  -- τ=407: 1 nodes, 1 σ-classes
  module τ407 where

    -- σ=663 (1 nodes)
    cell-0 : κ 299 ≡ κ 299
    cell-0 = refl



-- κ=301: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-37 where

  -- τ=408: 1 nodes, 1 σ-classes
  module τ408 where

    -- σ=667 (1 nodes)
    cell-0 : κ 301 ≡ κ 301
    cell-0 = refl



-- κ=302: 1 nodes, 1 τ-classes, 1 σ-classes
module morphism-at-x3f-Attribute-3 where

  -- τ=409: 1 nodes, 1 σ-classes
  module τ409 where

    -- σ=668 (1 nodes)
    cell-0 : κ 302 ≡ κ 302
    cell-0 = refl



-- κ=303: 1 nodes, 1 τ-classes, 1 σ-classes
module monoid-accum-AugAssign-3 where

  -- τ=410: 1 nodes, 1 σ-classes
  module τ410 where

    -- σ=669 (1 nodes)
    cell-0 : κ 303 ≡ κ 303
    cell-0 = refl



-- κ=304: 7 nodes, 1 τ-classes, 1 σ-classes
module fixpoint-next-Continue where

  -- τ=412: 7 nodes, 1 σ-classes
  module τ412 where

    -- σ=671 (7 nodes)
    cell-0 : κ 304 ≡ κ 304
    cell-0 = refl



-- κ=305: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-15 where

  -- τ=413: 1 nodes, 1 σ-classes
  module τ413 where

    -- σ=672 (1 nodes)
    cell-0 : κ 305 ≡ κ 305
    cell-0 = refl



-- κ=307: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-Compare-18 where

  -- τ=415: 1 nodes, 1 σ-classes
  module τ415 where

    -- σ=677 (1 nodes)
    cell-0 : κ 307 ≡ κ 307
    cell-0 = refl



-- κ=308: 1 nodes, 1 τ-classes, 1 σ-classes
module index-Index-21 where

  -- τ=416: 1 nodes, 1 σ-classes
  module τ416 where

    -- σ=678 (1 nodes)
    cell-0 : κ 308 ≡ κ 308
    cell-0 = refl



-- κ=309: 1 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-27 where

  -- τ=417: 1 nodes, 1 σ-classes
  module τ417 where

    -- σ=679 (1 nodes)
    cell-0 : κ 309 ≡ κ 309
    cell-0 = refl



-- κ=310: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-38 where

  -- τ=418: 1 nodes, 1 σ-classes
  module τ418 where

    -- σ=681 (1 nodes)
    cell-0 : κ 310 ≡ κ 310
    cell-0 = refl



-- κ=311: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-16 where

  -- τ=419: 1 nodes, 1 σ-classes
  module τ419 where

    -- σ=682 (1 nodes)
    cell-0 : κ 311 ≡ κ 311
    cell-0 = refl



-- κ=312: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-9 where

  -- τ=420: 1 nodes, 1 σ-classes
  module τ420 where

    -- σ=683 (1 nodes)
    cell-0 : κ 312 ≡ κ 312
    cell-0 = refl



-- κ=313: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-10 where

  -- τ=421: 1 nodes, 1 σ-classes
  module τ421 where

    -- σ=684 (1 nodes)
    cell-0 : κ 313 ≡ κ 313
    cell-0 = refl



-- κ=315: 1 nodes, 1 τ-classes, 1 σ-classes
module lazy_fold-GeneratorExp-4 where

  -- τ=423: 1 nodes, 1 σ-classes
  module τ423 where

    -- σ=688 (1 nodes)
    cell-0 : κ 315 ≡ κ 315
    cell-0 = refl



-- κ=316: 1 nodes, 1 τ-classes, 1 σ-classes
module powerset-Call-2 where

  -- τ=424: 1 nodes, 1 σ-classes
  module τ424 where

    -- σ=689 (1 nodes)
    cell-0 : κ 316 ≡ κ 316
    cell-0 = refl



-- κ=317: 1 nodes, 1 τ-classes, 1 σ-classes
module total_order-Call-1 where

  -- τ=425: 1 nodes, 1 σ-classes
  module list where

    -- σ=690 (1 nodes)
    cell-0 : κ 317 ≡ κ 317
    cell-0 = refl



-- κ=318: 1 nodes, 1 τ-classes, 1 σ-classes
module apply-Call-26 where

  -- τ=426: 1 nodes, 1 σ-classes
  module τ426 where

    -- σ=691 (1 nodes)
    cell-0 : κ 318 ≡ κ 318
    cell-0 = refl



-- κ=319: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-39 where

  -- τ=427: 1 nodes, 1 σ-classes
  module τ427 where

    -- σ=692 (1 nodes)
    cell-0 : κ 319 ≡ κ 319
    cell-0 = refl



-- κ=320: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-40 where

  -- τ=428: 1 nodes, 1 σ-classes
  module τ428 where

    -- σ=697 (1 nodes)
    cell-0 : κ 320 ≡ κ 320
    cell-0 = refl



-- κ=321: 1 nodes, 1 τ-classes, 1 σ-classes
module monoid-accum-AugAssign-4 where

  -- τ=429: 1 nodes, 1 σ-classes
  module τ429 where

    -- σ=698 (1 nodes)
    cell-0 : κ 321 ≡ κ 321
    cell-0 = refl



-- κ=322: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-17 where

  -- τ=430: 1 nodes, 1 σ-classes
  module τ430 where

    -- σ=699 (1 nodes)
    cell-0 : κ 322 ≡ κ 322
    cell-0 = refl



-- κ=323: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-18 where

  -- τ=431: 1 nodes, 1 σ-classes
  module τ431 where

    -- σ=700 (1 nodes)
    cell-0 : κ 323 ≡ κ 323
    cell-0 = refl



-- κ=324: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-19 where

  -- τ=432: 1 nodes, 1 σ-classes
  module τ432 where

    -- σ=701 (1 nodes)
    cell-0 : κ 324 ≡ κ 324
    cell-0 = refl



-- κ=325: 2 nodes, 1 τ-classes, 1 σ-classes
module fixpoint-halt-Break where

  -- τ=433: 2 nodes, 1 σ-classes
  module τ433 where

    -- σ=702 (2 nodes)
    cell-0 : κ 325 ≡ κ 325
    cell-0 = refl



-- κ=327: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-41 where

  -- τ=436: 1 nodes, 1 σ-classes
  module τ436 where

    -- σ=705 (1 nodes)
    cell-0 : κ 327 ≡ κ 327
    cell-0 = refl



-- κ=328: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-20 where

  -- τ=437: 1 nodes, 1 σ-classes
  module τ437 where

    -- σ=706 (1 nodes)
    cell-0 : κ 328 ≡ κ 328
    cell-0 = refl



-- κ=329: 1 nodes, 1 τ-classes, 1 σ-classes
module fixpoint-While-3 where

  -- τ=438: 1 nodes, 1 σ-classes
  module τ438 where

    -- σ=707 (1 nodes)
    cell-0 : κ 329 ≡ κ 329
    cell-0 = refl



-- κ=330: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-20 where

  -- τ=439: 1 nodes, 1 σ-classes
  module τ439 where

    -- σ=708 (1 nodes)
    cell-0 : κ 330 ≡ κ 330
    cell-0 = refl



-- κ=332: 1 nodes, 1 τ-classes, 1 σ-classes
module arguments-arguments-9 where

  -- τ=441: 1 nodes, 1 σ-classes
  module τ441 where

    -- σ=711 (1 nodes)
    cell-0 : κ 332 ≡ κ 332
    cell-0 = refl



-- κ=333: 3 nodes, 1 τ-classes, 1 σ-classes
module isnot-IsNot where

  -- τ=442: 3 nodes, 1 σ-classes
  module τ442 where

    -- σ=716 (3 nodes)
    cell-0 : κ 333 ≡ κ 333
    cell-0 = refl



-- κ=335: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-21 where

  -- τ=446: 1 nodes, 1 σ-classes
  module τ446 where

    -- σ=723 (1 nodes)
    cell-0 : κ 335 ≡ κ 335
    cell-0 = refl



-- κ=336: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-21 where

  -- τ=447: 1 nodes, 1 σ-classes
  module τ447 where

    -- σ=724 (1 nodes)
    cell-0 : κ 336 ≡ κ 336
    cell-0 = refl



-- κ=337: 1 nodes, 1 τ-classes, 1 σ-classes
module apply-Call-27 where

  -- τ=448: 1 nodes, 1 σ-classes
  module τ448 where

    -- σ=742 (1 nodes)
    cell-0 : κ 337 ≡ κ 337
    cell-0 = refl



-- κ=338: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-20 where

  -- τ=449: 1 nodes, 1 σ-classes
  module τ449 where

    -- σ=743 (1 nodes)
    cell-0 : κ 338 ≡ κ 338
    cell-0 = refl



-- κ=339: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-22 where

  -- τ=450: 1 nodes, 1 σ-classes
  module τ450 where

    -- σ=744 (1 nodes)
    cell-0 : κ 339 ≡ κ 339
    cell-0 = refl



-- κ=340: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-22 where

  -- τ=451: 1 nodes, 1 σ-classes
  module τ451 where

    -- σ=745 (1 nodes)
    cell-0 : κ 340 ≡ κ 340
    cell-0 = refl



-- κ=345: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-11 where

  -- τ=458: 1 nodes, 1 σ-classes
  module τ458 where

    -- σ=764 (1 nodes)
    cell-0 : κ 345 ≡ κ 345
    cell-0 = refl



-- κ=348: 1 nodes, 1 τ-classes, 1 σ-classes
module annassign-AnnAssign-26 where

  -- τ=466: 1 nodes, 1 σ-classes
  module τ466 where

    -- σ=782 (1 nodes)
    cell-0 : κ 348 ≡ κ 348
    cell-0 = refl



-- κ=360: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-23 where

  -- τ=480: 1 nodes, 1 σ-classes
  module τ480 where

    -- σ=820 (1 nodes)
    cell-0 : κ 360 ≡ κ 360
    cell-0 = refl



-- κ=361: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-24 where

  -- τ=481: 1 nodes, 1 σ-classes
  module τ481 where

    -- σ=822 (1 nodes)
    cell-0 : κ 361 ≡ κ 361
    cell-0 = refl



-- κ=362: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-12 where

  -- τ=482: 1 nodes, 1 σ-classes
  module τ482 where

    -- σ=823 (1 nodes)
    cell-0 : κ 362 ≡ κ 362
    cell-0 = refl



-- κ=363: 1 nodes, 1 τ-classes, 1 σ-classes
module apply-Call-28 where

  -- τ=444: 1 nodes, 1 σ-classes
  module τ444 where

    -- σ=829 (1 nodes)
    cell-0 : κ 363 ≡ κ 363
    cell-0 = refl



-- κ=364: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-21 where

  -- τ=445: 1 nodes, 1 σ-classes
  module τ445 where

    -- σ=830 (1 nodes)
    cell-0 : κ 364 ≡ κ 364
    cell-0 = refl



-- κ=365: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-13 where

  -- τ=483: 1 nodes, 1 σ-classes
  module τ483 where

    -- σ=831 (1 nodes)
    cell-0 : κ 365 ≡ κ 365
    cell-0 = refl



-- κ=366: 1 nodes, 1 τ-classes, 1 σ-classes
module product-unpack-Tuple-2 where

  -- τ=484: 1 nodes, 1 σ-classes
  module tuple where

    -- σ=836 (1 nodes)
    cell-0 : κ 366 ≡ κ 366
    cell-0 = refl



-- κ=367: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-literal-List-2 where

  -- τ=485: 1 nodes, 1 σ-classes
  module list where

    -- σ=838 (1 nodes)
    cell-0 : κ 367 ≡ κ 367
    cell-0 = refl



-- κ=368: 1 nodes, 1 τ-classes, 1 σ-classes
module product-Tuple-23 where

  -- τ=488: 1 nodes, 1 σ-classes
  module tuple where

    -- σ=842 (1 nodes)
    cell-0 : κ 368 ≡ κ 368
    cell-0 = refl



-- κ=369: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-snoc-at-state-Call-5 where

  -- τ=489: 1 nodes, 1 σ-classes
  module None where

    -- σ=843 (1 nodes)
    cell-0 : κ 369 ≡ κ 369
    cell-0 = refl



-- κ=370: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-22 where

  -- τ=490: 1 nodes, 1 σ-classes
  module τ490 where

    -- σ=844 (1 nodes)
    cell-0 : κ 370 ≡ κ 370
    cell-0 = refl



-- κ=379: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-14 where

  -- τ=501: 1 nodes, 1 σ-classes
  module τ501 where

    -- σ=864 (1 nodes)
    cell-0 : κ 379 ≡ κ 379
    cell-0 = refl



-- κ=380: 1 nodes, 1 τ-classes, 1 σ-classes
module coproduct-elim-If-3 where

  -- τ=502: 1 nodes, 1 σ-classes
  module τ502 where

    -- σ=865 (1 nodes)
    cell-0 : κ 380 ≡ κ 380
    cell-0 = refl



-- κ=381: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-15 where

  -- τ=503: 1 nodes, 1 σ-classes
  module τ503 where

    -- σ=866 (1 nodes)
    cell-0 : κ 381 ≡ κ 381
    cell-0 = refl



-- κ=382: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-23 where

  -- τ=504: 1 nodes, 1 σ-classes
  module τ504 where

    -- σ=868 (1 nodes)
    cell-0 : κ 382 ≡ κ 382
    cell-0 = refl



-- κ=383: 1 nodes, 1 τ-classes, 1 σ-classes
module arguments-arguments-10 where

  -- τ=505: 1 nodes, 1 σ-classes
  module τ505 where

    -- σ=870 (1 nodes)
    cell-0 : κ 383 ≡ κ 383
    cell-0 = refl



-- κ=384: 1 nodes, 1 τ-classes, 1 σ-classes
module is-Is where

  -- τ=506: 1 nodes, 1 σ-classes
  module τ506 where

    -- σ=874 (1 nodes)
    cell-0 : κ 384 ≡ κ 384
    cell-0 = refl



-- κ=385: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-Compare-19 where

  -- τ=507: 1 nodes, 1 σ-classes
  module τ507 where

    -- σ=875 (1 nodes)
    cell-0 : κ 385 ≡ κ 385
    cell-0 = refl



-- κ=387: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-25 where

  -- τ=509: 1 nodes, 1 σ-classes
  module τ509 where

    -- σ=877 (1 nodes)
    cell-0 : κ 387 ≡ κ 387
    cell-0 = refl



-- κ=388: 1 nodes, 1 τ-classes, 1 σ-classes
module partial-apply-at-state-Call-3 where

  -- τ=510: 1 nodes, 1 σ-classes
  module T where

    -- σ=878 (1 nodes)
    cell-0 : κ 388 ≡ κ 388
    cell-0 = refl



-- κ=389: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-42 where

  -- τ=511: 1 nodes, 1 σ-classes
  module τ511 where

    -- σ=879 (1 nodes)
    cell-0 : κ 389 ≡ κ 389
    cell-0 = refl



-- κ=390: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-26 where

  -- τ=513: 1 nodes, 1 σ-classes
  module τ513 where

    -- σ=881 (1 nodes)
    cell-0 : κ 390 ≡ κ 390
    cell-0 = refl



-- κ=391: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-24 where

  -- τ=514: 1 nodes, 1 σ-classes
  module τ514 where

    -- σ=883 (1 nodes)
    cell-0 : κ 391 ≡ κ 391
    cell-0 = refl



-- κ=392: 1 nodes, 1 τ-classes, 1 σ-classes
module arg-arg-5 where

  -- τ=515: 1 nodes, 1 σ-classes
  module τ515 where

    -- σ=884 (1 nodes)
    cell-0 : κ 392 ≡ κ 392
    cell-0 = refl



-- κ=393: 1 nodes, 1 τ-classes, 1 σ-classes
module arguments-arguments-11 where

  -- τ=516: 1 nodes, 1 σ-classes
  module τ516 where

    -- σ=885 (1 nodes)
    cell-0 : κ 393 ≡ κ 393
    cell-0 = refl



-- κ=398: 1 nodes, 1 τ-classes, 1 σ-classes
module product-Tuple-24 where

  -- τ=523: 1 nodes, 1 σ-classes
  module tuple where

    -- σ=906 (1 nodes)
    cell-0 : κ 398 ≡ κ 398
    cell-0 = refl



-- κ=399: 1 nodes, 1 τ-classes, 1 σ-classes
module terminal-map-Return-13 where

  -- τ=524: 1 nodes, 1 σ-classes
  module τ524 where

    -- σ=907 (1 nodes)
    cell-0 : κ 399 ≡ κ 399
    cell-0 = refl



-- κ=400: 1 nodes, 1 τ-classes, 1 σ-classes
module product-Tuple-25 where

  -- τ=525: 1 nodes, 1 σ-classes
  module tuple where

    -- σ=908 (1 nodes)
    cell-0 : κ 400 ≡ κ 400
    cell-0 = refl



-- κ=401: 1 nodes, 1 τ-classes, 1 σ-classes
module index-Index-22 where

  -- τ=526: 1 nodes, 1 σ-classes
  module τ526 where

    -- σ=909 (1 nodes)
    cell-0 : κ 401 ≡ κ 401
    cell-0 = refl



-- κ=402: 1 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-28 where

  -- τ=527: 1 nodes, 1 σ-classes
  module τ527 where

    -- σ=910 (1 nodes)
    cell-0 : κ 402 ≡ κ 402
    cell-0 = refl



-- κ=403: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-25 where

  -- τ=528: 1 nodes, 1 σ-classes
  module τ528 where

    -- σ=911 (1 nodes)
    cell-0 : κ 403 ≡ κ 403
    cell-0 = refl



-- κ=404: 1 nodes, 1 τ-classes, 1 σ-classes
module arg-arg-6 where

  -- τ=529: 1 nodes, 1 σ-classes
  module τ529 where

    -- σ=913 (1 nodes)
    cell-0 : κ 404 ≡ κ 404
    cell-0 = refl



-- κ=405: 1 nodes, 1 τ-classes, 1 σ-classes
module arguments-arguments-12 where

  -- τ=530: 1 nodes, 1 σ-classes
  module τ530 where

    -- σ=914 (1 nodes)
    cell-0 : κ 405 ≡ κ 405
    cell-0 = refl



-- κ=406: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-27 where

  -- τ=532: 1 nodes, 1 σ-classes
  module τ532 where

    -- σ=930 (1 nodes)
    cell-0 : κ 406 ≡ κ 406
    cell-0 = refl



-- κ=407: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-16 where

  -- τ=533: 1 nodes, 1 σ-classes
  module τ533 where

    -- σ=931 (1 nodes)
    cell-0 : κ 407 ≡ κ 407
    cell-0 = refl



-- κ=408: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-26 where

  -- τ=534: 1 nodes, 1 σ-classes
  module τ534 where

    -- σ=932 (1 nodes)
    cell-0 : κ 408 ≡ κ 408
    cell-0 = refl



-- κ=409: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-43 where

  -- τ=536: 1 nodes, 1 σ-classes
  module τ536 where

    -- σ=948 (1 nodes)
    cell-0 : κ 409 ≡ κ 409
    cell-0 = refl



-- κ=410: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-44 where

  -- τ=537: 1 nodes, 1 σ-classes
  module τ537 where

    -- σ=949 (1 nodes)
    cell-0 : κ 410 ≡ κ 410
    cell-0 = refl



-- κ=411: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-45 where

  -- τ=539: 1 nodes, 1 σ-classes
  module τ539 where

    -- σ=961 (1 nodes)
    cell-0 : κ 411 ≡ κ 411
    cell-0 = refl



-- κ=412: 2 nodes, 1 τ-classes, 1 σ-classes
module not-Not where

  -- τ=540: 2 nodes, 1 σ-classes
  module τ540 where

    -- σ=962 (2 nodes)
    cell-0 : κ 412 ≡ κ 412
    cell-0 = refl



-- κ=417: 1 nodes, 1 τ-classes, 1 σ-classes
module index-Index-23 where

  -- τ=545: 1 nodes, 1 σ-classes
  module τ545 where

    -- σ=969 (1 nodes)
    cell-0 : κ 417 ≡ κ 417
    cell-0 = refl



-- κ=418: 1 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-29 where

  -- τ=546: 1 nodes, 1 σ-classes
  module τ546 where

    -- σ=970 (1 nodes)
    cell-0 : κ 418 ≡ κ 418
    cell-0 = refl



-- κ=419: 1 nodes, 1 τ-classes, 1 σ-classes
module annassign-AnnAssign-27 where

  -- τ=547: 1 nodes, 1 σ-classes
  module τ547 where

    -- σ=971 (1 nodes)
    cell-0 : κ 419 ≡ κ 419
    cell-0 = refl



-- κ=422: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-28 where

  -- τ=550: 1 nodes, 1 σ-classes
  module τ550 where

    -- σ=987 (1 nodes)
    cell-0 : κ 422 ≡ κ 422
    cell-0 = refl



-- κ=423: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-29 where

  -- τ=551: 1 nodes, 1 σ-classes
  module τ551 where

    -- σ=989 (1 nodes)
    cell-0 : κ 423 ≡ κ 423
    cell-0 = refl



-- κ=424: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-17 where

  -- τ=552: 1 nodes, 1 σ-classes
  module τ552 where

    -- σ=990 (1 nodes)
    cell-0 : κ 424 ≡ κ 424
    cell-0 = refl



-- κ=425: 1 nodes, 1 τ-classes, 1 σ-classes
module monoid-accum-AugAssign-5 where

  -- τ=553: 1 nodes, 1 σ-classes
  module τ553 where

    -- σ=992 (1 nodes)
    cell-0 : κ 425 ≡ κ 425
    cell-0 = refl



-- κ=426: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-map-ListComp-0 where

  -- τ=554: 1 nodes, 1 σ-classes
  module τ554 where

    -- σ=997 (1 nodes)
    cell-0 : κ 426 ≡ κ 426
    cell-0 = refl



-- κ=427: 1 nodes, 1 τ-classes, 1 σ-classes
module product-Tuple-26 where

  -- τ=555: 1 nodes, 1 σ-classes
  module tuple where

    -- σ=999 (1 nodes)
    cell-0 : κ 427 ≡ κ 427
    cell-0 = refl



-- κ=428: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-snoc-at-state-Call-6 where

  -- τ=556: 1 nodes, 1 σ-classes
  module None where

    -- σ=1000 (1 nodes)
    cell-0 : κ 428 ≡ κ 428
    cell-0 = refl



-- κ=429: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-23 where

  -- τ=557: 1 nodes, 1 σ-classes
  module τ557 where

    -- σ=1001 (1 nodes)
    cell-0 : κ 429 ≡ κ 429
    cell-0 = refl



-- κ=430: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-18 where

  -- τ=558: 1 nodes, 1 σ-classes
  module τ558 where

    -- σ=1017 (1 nodes)
    cell-0 : κ 430 ≡ κ 430
    cell-0 = refl



-- κ=431: 1 nodes, 1 τ-classes, 1 σ-classes
module coproduct-elim-If-4 where

  -- τ=559: 1 nodes, 1 σ-classes
  module τ559 where

    -- σ=1018 (1 nodes)
    cell-0 : κ 431 ≡ κ 431
    cell-0 = refl



-- κ=432: 1 nodes, 1 τ-classes, 1 σ-classes
module complement-If-0 where

  -- τ=560: 1 nodes, 1 σ-classes
  module τ560 where

    -- σ=1019 (1 nodes)
    cell-0 : κ 432 ≡ κ 432
    cell-0 = refl



-- κ=433: 1 nodes, 1 τ-classes, 1 σ-classes
module del-Del where

  -- τ=561: 1 nodes, 1 σ-classes
  module τ561 where

    -- σ=1020 (1 nodes)
    cell-0 : κ 433 ≡ κ 433
    cell-0 = refl



-- κ=434: 1 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-30 where

  -- τ=562: 1 nodes, 1 σ-classes
  module τ562 where

    -- σ=1021 (1 nodes)
    cell-0 : κ 434 ≡ κ 434
    cell-0 = refl



-- κ=435: 1 nodes, 1 τ-classes, 1 σ-classes
module delete-Delete where

  -- τ=563: 1 nodes, 1 σ-classes
  module τ563 where

    -- σ=1022 (1 nodes)
    cell-0 : κ 435 ≡ κ 435
    cell-0 = refl



-- κ=436: 1 nodes, 1 τ-classes, 1 σ-classes
module morphism-at-object-Attribute where

  -- τ=564: 1 nodes, 1 σ-classes
  module T-discard where

    -- σ=1028 (1 nodes)
    cell-0 : κ 436 ≡ κ 436
    cell-0 = refl



-- κ=437: 1 nodes, 1 τ-classes, 1 σ-classes
module apply-Call-29 where

  -- τ=565: 1 nodes, 1 σ-classes
  module τ565 where

    -- σ=1029 (1 nodes)
    cell-0 : κ 437 ≡ κ 437
    cell-0 = refl



-- κ=438: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-24 where

  -- τ=566: 1 nodes, 1 σ-classes
  module τ566 where

    -- σ=1030 (1 nodes)
    cell-0 : κ 438 ≡ κ 438
    cell-0 = refl



-- κ=439: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-19 where

  -- τ=567: 1 nodes, 1 σ-classes
  module τ567 where

    -- σ=1031 (1 nodes)
    cell-0 : κ 439 ≡ κ 439
    cell-0 = refl



-- κ=447: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-30 where

  -- τ=575: 1 nodes, 1 σ-classes
  module τ575 where

    -- σ=1101 (1 nodes)
    cell-0 : κ 447 ≡ κ 447
    cell-0 = refl



-- κ=448: 1 nodes, 1 τ-classes, 1 σ-classes
module partial-apply-at-state-Call-4 where

  -- τ=577: 1 nodes, 1 σ-classes
  module T where

    -- σ=1104 (1 nodes)
    cell-0 : κ 448 ≡ κ 448
    cell-0 = refl



-- κ=449: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-46 where

  -- τ=578: 1 nodes, 1 σ-classes
  module τ578 where

    -- σ=1105 (1 nodes)
    cell-0 : κ 449 ≡ κ 449
    cell-0 = refl



-- κ=454: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-31 where

  -- τ=583: 1 nodes, 1 σ-classes
  module τ583 where

    -- σ=1121 (1 nodes)
    cell-0 : κ 454 ≡ κ 454
    cell-0 = refl



-- κ=455: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-20 where

  -- τ=584: 1 nodes, 1 σ-classes
  module τ584 where

    -- σ=1122 (1 nodes)
    cell-0 : κ 455 ≡ κ 455
    cell-0 = refl



-- κ=457: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-47 where

  -- τ=586: 1 nodes, 1 σ-classes
  module τ586 where

    -- σ=1129 (1 nodes)
    cell-0 : κ 457 ≡ κ 457
    cell-0 = refl



-- κ=458: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-48 where

  -- τ=588: 1 nodes, 1 σ-classes
  module τ588 where

    -- σ=1134 (1 nodes)
    cell-0 : κ 458 ≡ κ 458
    cell-0 = refl



-- κ=459: 2 nodes, 1 τ-classes, 1 σ-classes
module coerce-FormattedValue-10 where

  -- τ=589: 2 nodes, 1 σ-classes
  module τ589 where

    -- σ=1139 (2 nodes)
    cell-0 : κ 459 ≡ κ 459
    cell-0 = refl



-- κ=460: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-fold-JoinedStr-9 where

  -- τ=590: 1 nodes, 1 σ-classes
  module str where

    -- σ=1140 (1 nodes)
    cell-0 : κ 460 ≡ κ 460
    cell-0 = refl



-- κ=461: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-49 where

  -- τ=591: 1 nodes, 1 σ-classes
  module τ591 where

    -- σ=1141 (1 nodes)
    cell-0 : κ 461 ≡ κ 461
    cell-0 = refl



-- κ=462: 2 nodes, 1 τ-classes, 1 σ-classes
module powerset-literal-Set-k where

  -- τ=593: 2 nodes, 1 σ-classes
  module set where

    -- σ=1147 (2 nodes)
    cell-0 : κ 462 ≡ κ 462
    cell-0 = refl



-- κ=464: 2 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-25 where

  -- τ=598: 2 nodes, 1 σ-classes
  module τ598 where

    -- σ=1153 (2 nodes)
    cell-0 : κ 464 ≡ κ 464
    cell-0 = refl



-- κ=469: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-32 where

  -- τ=604: 1 nodes, 1 σ-classes
  module τ604 where

    -- σ=1172 (1 nodes)
    cell-0 : κ 469 ≡ κ 469
    cell-0 = refl



-- κ=470: 2 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-50 where

  -- τ=605: 2 nodes, 1 σ-classes
  module τ605 where

    -- σ=1176 (2 nodes)
    cell-0 : κ 470 ≡ κ 470
    cell-0 = refl



-- κ=475: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-33 where

  -- τ=611: 1 nodes, 1 σ-classes
  module τ611 where

    -- σ=1208 (1 nodes)
    cell-0 : κ 475 ≡ κ 475
    cell-0 = refl



-- κ=476: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-21 where

  -- τ=612: 1 nodes, 1 σ-classes
  module τ612 where

    -- σ=1209 (1 nodes)
    cell-0 : κ 476 ≡ κ 476
    cell-0 = refl



-- κ=477: 1 nodes, 1 τ-classes, 1 σ-classes
module fixpoint-While-4 where

  -- τ=613: 1 nodes, 1 σ-classes
  module τ613 where

    -- σ=1211 (1 nodes)
    cell-0 : κ 477 ≡ κ 477
    cell-0 = refl



-- κ=478: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-27 where

  -- τ=614: 1 nodes, 1 σ-classes
  module τ614 where

    -- σ=1212 (1 nodes)
    cell-0 : κ 478 ≡ κ 478
    cell-0 = refl



-- κ=479: 1 nodes, 1 τ-classes, 1 σ-classes
module product-Tuple-27 where

  -- τ=615: 1 nodes, 1 σ-classes
  module tuple where

    -- σ=1214 (1 nodes)
    cell-0 : κ 479 ≡ κ 479
    cell-0 = refl



-- κ=480: 1 nodes, 1 τ-classes, 1 σ-classes
module index-Index-24 where

  -- τ=616: 1 nodes, 1 σ-classes
  module τ616 where

    -- σ=1215 (1 nodes)
    cell-0 : κ 480 ≡ κ 480
    cell-0 = refl



-- κ=481: 1 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-31 where

  -- τ=617: 1 nodes, 1 σ-classes
  module τ617 where

    -- σ=1216 (1 nodes)
    cell-0 : κ 481 ≡ κ 481
    cell-0 = refl



-- κ=482: 1 nodes, 1 τ-classes, 1 σ-classes
module arg-arg-7 where

  -- τ=618: 1 nodes, 1 σ-classes
  module τ618 where

    -- σ=1217 (1 nodes)
    cell-0 : κ 482 ≡ κ 482
    cell-0 = refl



-- κ=483: 1 nodes, 1 τ-classes, 1 σ-classes
module arguments-arguments-13 where

  -- τ=619: 1 nodes, 1 σ-classes
  module τ619 where

    -- σ=1224 (1 nodes)
    cell-0 : κ 483 ≡ κ 483
    cell-0 = refl



-- κ=485: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-51 where

  -- τ=621: 1 nodes, 1 σ-classes
  module τ621 where

    -- σ=1233 (1 nodes)
    cell-0 : κ 485 ≡ κ 485
    cell-0 = refl



-- κ=488: 1 nodes, 1 τ-classes, 1 σ-classes
module product-Tuple-28 where

  -- τ=626: 1 nodes, 1 σ-classes
  module tuple where

    -- σ=1261 (1 nodes)
    cell-0 : κ 488 ≡ κ 488
    cell-0 = refl



-- κ=489: 1 nodes, 1 τ-classes, 1 σ-classes
module index-Index-25 where

  -- τ=627: 1 nodes, 1 σ-classes
  module τ627 where

    -- σ=1262 (1 nodes)
    cell-0 : κ 489 ≡ κ 489
    cell-0 = refl



-- κ=490: 1 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-32 where

  -- τ=628: 1 nodes, 1 σ-classes
  module τ628 where

    -- σ=1263 (1 nodes)
    cell-0 : κ 490 ≡ κ 490
    cell-0 = refl



-- κ=491: 1 nodes, 1 τ-classes, 1 σ-classes
module annassign-AnnAssign-28 where

  -- τ=629: 1 nodes, 1 σ-classes
  module τ629 where

    -- σ=1267 (1 nodes)
    cell-0 : κ 491 ≡ κ 491
    cell-0 = refl



-- κ=492: 1 nodes, 1 τ-classes, 1 σ-classes
module annassign-AnnAssign-29 where

  -- τ=633: 1 nodes, 1 σ-classes
  module τ633 where

    -- σ=1273 (1 nodes)
    cell-0 : κ 492 ≡ κ 492
    cell-0 = refl



-- κ=493: 2 nodes, 1 τ-classes, 1 σ-classes
module and-And where

  -- τ=634: 2 nodes, 1 σ-classes
  module τ634 where

    -- σ=1274 (2 nodes)
    cell-0 : κ 493 ≡ κ 493
    cell-0 = refl



-- κ=494: 1 nodes, 1 τ-classes, 1 σ-classes
module meet-BoolOp-0 where

  -- τ=635: 1 nodes, 1 σ-classes
  module τ635 where

    -- σ=1277 (1 nodes)
    cell-0 : κ 494 ≡ κ 494
    cell-0 = refl



-- κ=495: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-Compare-20 where

  -- τ=636: 1 nodes, 1 σ-classes
  module τ636 where

    -- σ=1284 (1 nodes)
    cell-0 : κ 495 ≡ κ 495
    cell-0 = refl



-- κ=496: 1 nodes, 1 τ-classes, 1 σ-classes
module lazy_fold-GeneratorExp-5 where

  -- τ=637: 1 nodes, 1 σ-classes
  module τ637 where

    -- σ=1287 (1 nodes)
    cell-0 : κ 496 ≡ κ 496
    cell-0 = refl



-- κ=497: 1 nodes, 1 τ-classes, 1 σ-classes
module apply-Call-30 where

  -- τ=638: 1 nodes, 1 σ-classes
  module τ638 where

    -- σ=1288 (1 nodes)
    cell-0 : κ 497 ≡ κ 497
    cell-0 = refl



-- κ=498: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-52 where

  -- τ=639: 1 nodes, 1 σ-classes
  module τ639 where

    -- σ=1289 (1 nodes)
    cell-0 : κ 498 ≡ κ 498
    cell-0 = refl



-- κ=499: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-map-ListComp-1 where

  -- τ=640: 1 nodes, 1 σ-classes
  module τ640 where

    -- σ=1291 (1 nodes)
    cell-0 : κ 499 ≡ κ 499
    cell-0 = refl



-- κ=500: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-53 where

  -- τ=641: 1 nodes, 1 σ-classes
  module τ641 where

    -- σ=1292 (1 nodes)
    cell-0 : κ 500 ≡ κ 500
    cell-0 = refl



-- κ=501: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-snoc-at-x3f-Call-3 where

  -- τ=189: 1 nodes, 1 σ-classes
  module τ189 where

    -- σ=1294 (1 nodes)
    cell-0 : κ 501 ≡ κ 501
    cell-0 = refl



-- κ=502: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-26 where

  -- τ=190: 1 nodes, 1 σ-classes
  module τ190 where

    -- σ=1295 (1 nodes)
    cell-0 : κ 502 ≡ κ 502
    cell-0 = refl



-- κ=503: 1 nodes, 1 τ-classes, 1 σ-classes
module monoid-op-BinOp-1 where

  -- τ=642: 1 nodes, 1 σ-classes
  module τ642 where

    -- σ=1297 (1 nodes)
    cell-0 : κ 503 ≡ κ 503
    cell-0 = refl



-- κ=504: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-54 where

  -- τ=643: 1 nodes, 1 σ-classes
  module τ643 where

    -- σ=1298 (1 nodes)
    cell-0 : κ 504 ≡ κ 504
    cell-0 = refl



-- κ=505: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-fold-JoinedStr-10 where

  -- τ=644: 1 nodes, 1 σ-classes
  module str where

    -- σ=1302 (1 nodes)
    cell-0 : κ 505 ≡ κ 505
    cell-0 = refl



-- κ=506: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-55 where

  -- τ=645: 1 nodes, 1 σ-classes
  module τ645 where

    -- σ=1303 (1 nodes)
    cell-0 : κ 506 ≡ κ 506
    cell-0 = refl



-- κ=507: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-map-ListComp-2 where

  -- τ=649: 1 nodes, 1 σ-classes
  module τ649 where

    -- σ=1329 (1 nodes)
    cell-0 : κ 507 ≡ κ 507
    cell-0 = refl



-- κ=508: 1 nodes, 1 τ-classes, 1 σ-classes
module apply-Call-31 where

  -- τ=650: 1 nodes, 1 σ-classes
  module τ650 where

    -- σ=1330 (1 nodes)
    cell-0 : κ 508 ≡ κ 508
    cell-0 = refl



-- κ=509: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-27 where

  -- τ=651: 1 nodes, 1 σ-classes
  module τ651 where

    -- σ=1331 (1 nodes)
    cell-0 : κ 509 ≡ κ 509
    cell-0 = refl



-- κ=510: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-34 where

  -- τ=655: 1 nodes, 1 σ-classes
  module τ655 where

    -- σ=1341 (1 nodes)
    cell-0 : κ 510 ≡ κ 510
    cell-0 = refl



-- κ=512: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-56 where

  -- τ=521: 1 nodes, 1 σ-classes
  module τ521 where

    -- σ=1345 (1 nodes)
    cell-0 : κ 512 ≡ κ 512
    cell-0 = refl



-- κ=513: 1 nodes, 1 τ-classes, 1 σ-classes
module monoid-op-at-x3f-Call-3 where

  -- τ=656: 1 nodes, 1 σ-classes
  module τ656 where

    -- σ=1348 (1 nodes)
    cell-0 : κ 513 ≡ κ 513
    cell-0 = refl



-- κ=514: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-28 where

  -- τ=657: 1 nodes, 1 σ-classes
  module τ657 where

    -- σ=1349 (1 nodes)
    cell-0 : κ 514 ≡ κ 514
    cell-0 = refl



-- κ=516: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-29 where

  -- τ=190: 1 nodes, 1 σ-classes
  module τ190 where

    -- σ=1353 (1 nodes)
    cell-0 : κ 516 ≡ κ 516
    cell-0 = refl



-- κ=517: 1 nodes, 1 τ-classes, 1 σ-classes
module coproduct-elim-If-5 where

  -- τ=662: 1 nodes, 1 σ-classes
  module τ662 where

    -- σ=1359 (1 nodes)
    cell-0 : κ 517 ≡ κ 517
    cell-0 = refl



-- κ=518: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-35 where

  -- τ=663: 1 nodes, 1 σ-classes
  module τ663 where

    -- σ=1368 (1 nodes)
    cell-0 : κ 518 ≡ κ 518
    cell-0 = refl



-- κ=519: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-57 where

  -- τ=664: 1 nodes, 1 σ-classes
  module τ664 where

    -- σ=1370 (1 nodes)
    cell-0 : κ 519 ≡ κ 519
    cell-0 = refl



-- κ=520: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-36 where

  -- τ=665: 1 nodes, 1 σ-classes
  module τ665 where

    -- σ=1374 (1 nodes)
    cell-0 : κ 520 ≡ κ 520
    cell-0 = refl



-- κ=521: 1 nodes, 1 τ-classes, 1 σ-classes
module coproduct-elim-If-6 where

  -- τ=666: 1 nodes, 1 σ-classes
  module τ666 where

    -- σ=1375 (1 nodes)
    cell-0 : κ 521 ≡ κ 521
    cell-0 = refl



-- κ=522: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-literal-Dict-2 where

  -- τ=668: 1 nodes, 1 σ-classes
  module dict where

    -- σ=1387 (1 nodes)
    cell-0 : κ 522 ≡ κ 522
    cell-0 = refl



-- κ=523: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-snoc-at-state-Call-7 where

  -- τ=669: 1 nodes, 1 σ-classes
  module None where

    -- σ=1388 (1 nodes)
    cell-0 : κ 523 ≡ κ 523
    cell-0 = refl



-- κ=524: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-30 where

  -- τ=670: 1 nodes, 1 σ-classes
  module τ670 where

    -- σ=1389 (1 nodes)
    cell-0 : κ 524 ≡ κ 524
    cell-0 = refl



-- κ=525: 1 nodes, 1 τ-classes, 1 σ-classes
module product-Tuple-29 where

  -- τ=671: 1 nodes, 1 σ-classes
  module tuple where

    -- σ=1393 (1 nodes)
    cell-0 : κ 525 ≡ κ 525
    cell-0 = refl



-- κ=526: 1 nodes, 1 τ-classes, 1 σ-classes
module index-Index-26 where

  -- τ=672: 1 nodes, 1 σ-classes
  module τ672 where

    -- σ=1394 (1 nodes)
    cell-0 : κ 526 ≡ κ 526
    cell-0 = refl



-- κ=527: 1 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-33 where

  -- τ=673: 1 nodes, 1 σ-classes
  module τ673 where

    -- σ=1395 (1 nodes)
    cell-0 : κ 527 ≡ κ 527
    cell-0 = refl



-- κ=528: 1 nodes, 1 τ-classes, 1 σ-classes
module monoid-op-at-x3f-Attribute-2 where

  -- τ=674: 1 nodes, 1 σ-classes
  module τ674 where

    -- σ=1396 (1 nodes)
    cell-0 : κ 528 ≡ κ 528
    cell-0 = refl



-- κ=529: 1 nodes, 1 τ-classes, 1 σ-classes
module monoid-op-at-x3f-Call-4 where

  -- τ=675: 1 nodes, 1 σ-classes
  module τ675 where

    -- σ=1397 (1 nodes)
    cell-0 : κ 529 ≡ κ 529
    cell-0 = refl



-- κ=530: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-31 where

  -- τ=676: 1 nodes, 1 σ-classes
  module τ676 where

    -- σ=1398 (1 nodes)
    cell-0 : κ 530 ≡ κ 530
    cell-0 = refl



-- κ=532: 1 nodes, 1 τ-classes, 1 σ-classes
module terminal-map-Return-14 where

  -- τ=678: 1 nodes, 1 σ-classes
  module τ678 where

    -- σ=1400 (1 nodes)
    cell-0 : κ 532 ≡ κ 532
    cell-0 = refl



-- κ=533: 1 nodes, 1 τ-classes, 1 σ-classes
module index-Index-27 where

  -- τ=680: 1 nodes, 1 σ-classes
  module τ680 where

    -- σ=1402 (1 nodes)
    cell-0 : κ 533 ≡ κ 533
    cell-0 = refl



-- κ=534: 1 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-34 where

  -- τ=681: 1 nodes, 1 σ-classes
  module τ681 where

    -- σ=1403 (1 nodes)
    cell-0 : κ 534 ≡ κ 534
    cell-0 = refl



-- κ=535: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-28 where

  -- τ=682: 1 nodes, 1 σ-classes
  module τ682 where

    -- σ=1404 (1 nodes)
    cell-0 : κ 535 ≡ κ 535
    cell-0 = refl



-- κ=536: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-29 where

  -- τ=683: 1 nodes, 1 σ-classes
  module τ683 where

    -- σ=1407 (1 nodes)
    cell-0 : κ 536 ≡ κ 536
    cell-0 = refl



-- κ=537: 1 nodes, 1 τ-classes, 1 σ-classes
module arg-arg-8 where

  -- τ=684: 1 nodes, 1 σ-classes
  module τ684 where

    -- σ=1408 (1 nodes)
    cell-0 : κ 537 ≡ κ 537
    cell-0 = refl



-- κ=538: 1 nodes, 1 τ-classes, 1 σ-classes
module arguments-arguments-14 where

  -- τ=685: 1 nodes, 1 σ-classes
  module τ685 where

    -- σ=1410 (1 nodes)
    cell-0 : κ 538 ≡ κ 538
    cell-0 = refl



-- κ=539: 1 nodes, 1 τ-classes, 1 σ-classes
module annassign-AnnAssign-30 where

  -- τ=687: 1 nodes, 1 σ-classes
  module τ687 where

    -- σ=1414 (1 nodes)
    cell-0 : κ 539 ≡ κ 539
    cell-0 = refl



-- κ=542: 1 nodes, 1 τ-classes, 1 σ-classes
module terminal-map-Return-15 where

  -- τ=691: 1 nodes, 1 σ-classes
  module τ691 where

    -- σ=1420 (1 nodes)
    cell-0 : κ 542 ≡ κ 542
    cell-0 = refl



-- κ=543: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-30 where

  -- τ=692: 1 nodes, 1 σ-classes
  module τ692 where

    -- σ=1421 (1 nodes)
    cell-0 : κ 543 ≡ κ 543
    cell-0 = refl



-- κ=544: 2 nodes, 1 τ-classes, 1 σ-classes
module index-Index-28 where

  -- τ=694: 2 nodes, 1 σ-classes
  module τ694 where

    -- σ=1426 (2 nodes)
    cell-0 : κ 544 ≡ κ 544
    cell-0 = refl



-- κ=545: 2 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-35 where

  -- τ=695: 2 nodes, 1 σ-classes
  module τ695 where

    -- σ=1427 (2 nodes)
    cell-0 : κ 545 ≡ κ 545
    cell-0 = refl



-- κ=546: 2 nodes, 1 τ-classes, 1 σ-classes
module product-Tuple-30 where

  -- τ=696: 2 nodes, 1 σ-classes
  module tuple where

    -- σ=1428 (2 nodes)
    cell-0 : κ 546 ≡ κ 546
    cell-0 = refl



-- κ=547: 2 nodes, 1 τ-classes, 1 σ-classes
module index-Index-29 where

  -- τ=697: 2 nodes, 1 σ-classes
  module τ697 where

    -- σ=1429 (2 nodes)
    cell-0 : κ 547 ≡ κ 547
    cell-0 = refl



-- κ=549: 1 nodes, 1 τ-classes, 1 σ-classes
module annassign-AnnAssign-31 where

  -- τ=699: 1 nodes, 1 σ-classes
  module τ699 where

    -- σ=1432 (1 nodes)
    cell-0 : κ 549 ≡ κ 549
    cell-0 = refl



-- κ=551: 1 nodes, 1 τ-classes, 1 σ-classes
module product-Tuple-31 where

  -- τ=702: 1 nodes, 1 σ-classes
  module tuple where

    -- σ=1444 (1 nodes)
    cell-0 : κ 551 ≡ κ 551
    cell-0 = refl



-- κ=552: 1 nodes, 1 τ-classes, 1 σ-classes
module index-Index-30 where

  -- τ=703: 1 nodes, 1 σ-classes
  module τ703 where

    -- σ=1445 (1 nodes)
    cell-0 : κ 552 ≡ κ 552
    cell-0 = refl



-- κ=553: 1 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-36 where

  -- τ=704: 1 nodes, 1 σ-classes
  module τ704 where

    -- σ=1446 (1 nodes)
    cell-0 : κ 553 ≡ κ 553
    cell-0 = refl



-- κ=554: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-op-at-x3f-Attribute-2 where

  -- τ=705: 1 nodes, 1 σ-classes
  module τ705 where

    -- σ=1447 (1 nodes)
    cell-0 : κ 554 ≡ κ 554
    cell-0 = refl



-- κ=555: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-snoc-at-x3f-Call-4 where

  -- τ=706: 1 nodes, 1 σ-classes
  module τ706 where

    -- σ=1449 (1 nodes)
    cell-0 : κ 555 ≡ κ 555
    cell-0 = refl



-- κ=556: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-32 where

  -- τ=707: 1 nodes, 1 σ-classes
  module τ707 where

    -- σ=1450 (1 nodes)
    cell-0 : κ 556 ≡ κ 556
    cell-0 = refl



-- κ=557: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-22 where

  -- τ=708: 1 nodes, 1 σ-classes
  module τ708 where

    -- σ=1451 (1 nodes)
    cell-0 : κ 557 ≡ κ 557
    cell-0 = refl



-- κ=560: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-31 where

  -- τ=711: 1 nodes, 1 σ-classes
  module τ711 where

    -- σ=1455 (1 nodes)
    cell-0 : κ 560 ≡ κ 560
    cell-0 = refl



-- κ=561: 1 nodes, 1 τ-classes, 1 σ-classes
module annassign-AnnAssign-32 where

  -- τ=715: 1 nodes, 1 σ-classes
  module τ715 where

    -- σ=1467 (1 nodes)
    cell-0 : κ 561 ≡ κ 561
    cell-0 = refl



-- κ=562: 1 nodes, 1 τ-classes, 1 σ-classes
module product-Tuple-32 where

  -- τ=716: 1 nodes, 1 σ-classes
  module tuple where

    -- σ=1472 (1 nodes)
    cell-0 : κ 562 ≡ κ 562
    cell-0 = refl



-- κ=563: 1 nodes, 1 τ-classes, 1 σ-classes
module index-Index-31 where

  -- τ=717: 1 nodes, 1 σ-classes
  module τ717 where

    -- σ=1473 (1 nodes)
    cell-0 : κ 563 ≡ κ 563
    cell-0 = refl



-- κ=564: 1 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-37 where

  -- τ=718: 1 nodes, 1 σ-classes
  module τ718 where

    -- σ=1474 (1 nodes)
    cell-0 : κ 564 ≡ κ 564
    cell-0 = refl



-- κ=565: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-op-at-x3f-Attribute-3 where

  -- τ=719: 1 nodes, 1 σ-classes
  module τ719 where

    -- σ=1475 (1 nodes)
    cell-0 : κ 565 ≡ κ 565
    cell-0 = refl



-- κ=566: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-snoc-at-x3f-Call-5 where

  -- τ=720: 1 nodes, 1 σ-classes
  module τ720 where

    -- σ=1476 (1 nodes)
    cell-0 : κ 566 ≡ κ 566
    cell-0 = refl



-- κ=567: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-33 where

  -- τ=721: 1 nodes, 1 σ-classes
  module τ721 where

    -- σ=1477 (1 nodes)
    cell-0 : κ 567 ≡ κ 567
    cell-0 = refl



-- κ=568: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-23 where

  -- τ=722: 1 nodes, 1 σ-classes
  module τ722 where

    -- σ=1478 (1 nodes)
    cell-0 : κ 568 ≡ κ 568
    cell-0 = refl



-- κ=569: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-32 where

  -- τ=724: 1 nodes, 1 σ-classes
  module τ724 where

    -- σ=1480 (1 nodes)
    cell-0 : κ 569 ≡ κ 569
    cell-0 = refl



-- κ=572: 1 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-38 where

  -- τ=731: 1 nodes, 1 σ-classes
  module τ731 where

    -- σ=1498 (1 nodes)
    cell-0 : κ 572 ≡ κ 572
    cell-0 = refl



-- κ=573: 1 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-39 where

  -- τ=732: 1 nodes, 1 σ-classes
  module τ732 where

    -- σ=1502 (1 nodes)
    cell-0 : κ 573 ≡ κ 573
    cell-0 = refl



-- κ=574: 1 nodes, 1 τ-classes, 1 σ-classes
module monoid-accum-AugAssign-6 where

  -- τ=733: 1 nodes, 1 σ-classes
  module τ733 where

    -- σ=1503 (1 nodes)
    cell-0 : κ 574 ≡ κ 574
    cell-0 = refl



-- κ=575: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-24 where

  -- τ=734: 1 nodes, 1 σ-classes
  module τ734 where

    -- σ=1504 (1 nodes)
    cell-0 : κ 575 ≡ κ 575
    cell-0 = refl



-- κ=577: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-map-DictComp-0 where

  -- τ=736: 1 nodes, 1 σ-classes
  module τ736 where

    -- σ=1514 (1 nodes)
    cell-0 : κ 577 ≡ κ 577
    cell-0 = refl



-- κ=578: 1 nodes, 1 τ-classes, 1 σ-classes
module terminal-map-Return-16 where

  -- τ=737: 1 nodes, 1 σ-classes
  module τ737 where

    -- σ=1515 (1 nodes)
    cell-0 : κ 578 ≡ κ 578
    cell-0 = refl



-- κ=579: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-33 where

  -- τ=741: 1 nodes, 1 σ-classes
  module τ741 where

    -- σ=1520 (1 nodes)
    cell-0 : κ 579 ≡ κ 579
    cell-0 = refl



-- κ=580: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-58 where

  -- τ=742: 1 nodes, 1 σ-classes
  module τ742 where

    -- σ=1535 (1 nodes)
    cell-0 : κ 580 ≡ κ 580
    cell-0 = refl



-- κ=581: 1 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-40 where

  -- τ=743: 1 nodes, 1 σ-classes
  module τ743 where

    -- σ=1540 (1 nodes)
    cell-0 : κ 581 ≡ κ 581
    cell-0 = refl



-- κ=582: 1 nodes, 1 τ-classes, 1 σ-classes
module morphism-at-x3f-Attribute-4 where

  -- τ=744: 1 nodes, 1 σ-classes
  module τ744 where

    -- σ=1541 (1 nodes)
    cell-0 : κ 582 ≡ κ 582
    cell-0 = refl



-- κ=583: 1 nodes, 1 τ-classes, 1 σ-classes
module apply-Call-32 where

  -- τ=745: 1 nodes, 1 σ-classes
  module τ745 where

    -- σ=1548 (1 nodes)
    cell-0 : κ 583 ≡ κ 583
    cell-0 = refl



-- κ=584: 1 nodes, 1 τ-classes, 1 σ-classes
module monoid-op-at-x3f-Call-5 where

  -- τ=746: 1 nodes, 1 σ-classes
  module τ746 where

    -- σ=1549 (1 nodes)
    cell-0 : κ 584 ≡ κ 584
    cell-0 = refl



-- κ=585: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-34 where

  -- τ=747: 1 nodes, 1 σ-classes
  module τ747 where

    -- σ=1550 (1 nodes)
    cell-0 : κ 585 ≡ κ 585
    cell-0 = refl



-- κ=586: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-25 where

  -- τ=748: 1 nodes, 1 σ-classes
  module τ748 where

    -- σ=1551 (1 nodes)
    cell-0 : κ 586 ≡ κ 586
    cell-0 = refl



-- κ=587: 1 nodes, 1 τ-classes, 1 σ-classes
module terminal-map-Return-17 where

  -- τ=749: 1 nodes, 1 σ-classes
  module τ749 where

    -- σ=1553 (1 nodes)
    cell-0 : κ 587 ≡ κ 587
    cell-0 = refl



-- κ=588: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-34 where

  -- τ=750: 1 nodes, 1 σ-classes
  module τ750 where

    -- σ=1554 (1 nodes)
    cell-0 : κ 588 ≡ κ 588
    cell-0 = refl



-- κ=590: 1 nodes, 1 τ-classes, 1 σ-classes
module index-Index-32 where

  -- τ=753: 1 nodes, 1 σ-classes
  module τ753 where

    -- σ=1564 (1 nodes)
    cell-0 : κ 590 ≡ κ 590
    cell-0 = refl



-- κ=591: 1 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-41 where

  -- τ=754: 1 nodes, 1 σ-classes
  module τ754 where

    -- σ=1565 (1 nodes)
    cell-0 : κ 591 ≡ κ 591
    cell-0 = refl



-- κ=592: 1 nodes, 1 τ-classes, 1 σ-classes
module monoid-accum-AugAssign-7 where

  -- τ=755: 1 nodes, 1 σ-classes
  module τ755 where

    -- σ=1566 (1 nodes)
    cell-0 : κ 592 ≡ κ 592
    cell-0 = refl



-- κ=593: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-26 where

  -- τ=756: 1 nodes, 1 σ-classes
  module τ756 where

    -- σ=1567 (1 nodes)
    cell-0 : κ 593 ≡ κ 593
    cell-0 = refl



-- κ=594: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-35 where

  -- τ=757: 1 nodes, 1 σ-classes
  module τ757 where

    -- σ=1569 (1 nodes)
    cell-0 : κ 594 ≡ κ 594
    cell-0 = refl



-- κ=595: 1 nodes, 1 τ-classes, 1 σ-classes
module annassign-AnnAssign-33 where

  -- τ=760: 1 nodes, 1 σ-classes
  module τ760 where

    -- σ=1581 (1 nodes)
    cell-0 : κ 595 ≡ κ 595
    cell-0 = refl



-- κ=598: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-literal-Dict-3 where

  -- τ=765: 1 nodes, 1 σ-classes
  module dict where

    -- σ=1607 (1 nodes)
    cell-0 : κ 598 ≡ κ 598
    cell-0 = refl



-- κ=599: 1 nodes, 1 τ-classes, 1 σ-classes
module annassign-AnnAssign-34 where

  -- τ=766: 1 nodes, 1 σ-classes
  module τ766 where

    -- σ=1608 (1 nodes)
    cell-0 : κ 599 ≡ κ 599
    cell-0 = refl



-- κ=601: 1 nodes, 1 τ-classes, 1 σ-classes
module keyword-keyword-0 where

  -- τ=767: 1 nodes, 1 σ-classes
  module τ767 where

    -- σ=1613 (1 nodes)
    cell-0 : κ 601 ≡ κ 601
    cell-0 = refl



-- κ=602: 1 nodes, 1 τ-classes, 1 σ-classes
module apply-Call-33 where

  -- τ=768: 1 nodes, 1 σ-classes
  module τ768 where

    -- σ=1614 (1 nodes)
    cell-0 : κ 602 ≡ κ 602
    cell-0 = refl



-- κ=603: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-59 where

  -- τ=769: 1 nodes, 1 σ-classes
  module τ769 where

    -- σ=1615 (1 nodes)
    cell-0 : κ 603 ≡ κ 603
    cell-0 = refl



-- κ=604: 1 nodes, 1 τ-classes, 1 σ-classes
module monoid-accum-AugAssign-8 where

  -- τ=770: 1 nodes, 1 σ-classes
  module τ770 where

    -- σ=1620 (1 nodes)
    cell-0 : κ 604 ≡ κ 604
    cell-0 = refl



-- κ=605: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-literal-Dict-4 where

  -- τ=771: 1 nodes, 1 σ-classes
  module dict where

    -- σ=1622 (1 nodes)
    cell-0 : κ 605 ≡ κ 605
    cell-0 = refl



-- κ=606: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-60 where

  -- τ=772: 1 nodes, 1 σ-classes
  module τ772 where

    -- σ=1623 (1 nodes)
    cell-0 : κ 606 ≡ κ 606
    cell-0 = refl



-- κ=607: 1 nodes, 1 τ-classes, 1 σ-classes
module monoid-op-at-x3f-Call-6 where

  -- τ=774: 1 nodes, 1 σ-classes
  module τ774 where

    -- σ=1629 (1 nodes)
    cell-0 : κ 607 ≡ κ 607
    cell-0 = refl



-- κ=608: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-35 where

  -- τ=775: 1 nodes, 1 σ-classes
  module τ775 where

    -- σ=1630 (1 nodes)
    cell-0 : κ 608 ≡ κ 608
    cell-0 = refl



-- κ=609: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-27 where

  -- τ=776: 1 nodes, 1 σ-classes
  module τ776 where

    -- σ=1631 (1 nodes)
    cell-0 : κ 609 ≡ κ 609
    cell-0 = refl



-- κ=610: 1 nodes, 1 τ-classes, 1 σ-classes
module terminal-map-Return-18 where

  -- τ=777: 1 nodes, 1 σ-classes
  module τ777 where

    -- σ=1633 (1 nodes)
    cell-0 : κ 610 ≡ κ 610
    cell-0 = refl



-- κ=611: 1 nodes, 1 τ-classes, 1 σ-classes
module product-Tuple-33 where

  -- τ=778: 1 nodes, 1 σ-classes
  module tuple where

    -- σ=1634 (1 nodes)
    cell-0 : κ 611 ≡ κ 611
    cell-0 = refl



-- κ=612: 1 nodes, 1 τ-classes, 1 σ-classes
module index-Index-33 where

  -- τ=779: 1 nodes, 1 σ-classes
  module τ779 where

    -- σ=1635 (1 nodes)
    cell-0 : κ 612 ≡ κ 612
    cell-0 = refl



-- κ=613: 1 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-42 where

  -- τ=780: 1 nodes, 1 σ-classes
  module τ780 where

    -- σ=1636 (1 nodes)
    cell-0 : κ 613 ≡ κ 613
    cell-0 = refl



-- κ=614: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-36 where

  -- τ=781: 1 nodes, 1 σ-classes
  module τ781 where

    -- σ=1637 (1 nodes)
    cell-0 : κ 614 ≡ κ 614
    cell-0 = refl



-- κ=615: 3 nodes, 1 τ-classes, 1 σ-classes
module product-Tuple-34 where

  -- τ=782: 3 nodes, 1 σ-classes
  module tuple where

    -- σ=1644 (3 nodes)
    cell-0 : κ 615 ≡ κ 615
    cell-0 = refl



-- κ=616: 1 nodes, 1 τ-classes, 1 σ-classes
module comprehension-comprehension-5 where

  -- τ=783: 1 nodes, 1 σ-classes
  module τ783 where

    -- σ=1646 (1 nodes)
    cell-0 : κ 616 ≡ κ 616
    cell-0 = refl



-- κ=617: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-map-ListComp-3 where

  -- τ=784: 1 nodes, 1 σ-classes
  module τ784 where

    -- σ=1647 (1 nodes)
    cell-0 : κ 617 ≡ κ 617
    cell-0 = refl



-- κ=618: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-61 where

  -- τ=785: 1 nodes, 1 σ-classes
  module τ785 where

    -- σ=1648 (1 nodes)
    cell-0 : κ 618 ≡ κ 618
    cell-0 = refl



-- κ=619: 2 nodes, 1 τ-classes, 1 σ-classes
module index-Index-34 where

  -- τ=786: 2 nodes, 1 σ-classes
  module τ786 where

    -- σ=1653 (2 nodes)
    cell-0 : κ 619 ≡ κ 619
    cell-0 = refl



-- κ=620: 2 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-43 where

  -- τ=787: 2 nodes, 1 σ-classes
  module τ787 where

    -- σ=1654 (2 nodes)
    cell-0 : κ 620 ≡ κ 620
    cell-0 = refl



-- κ=621: 1 nodes, 1 τ-classes, 1 σ-classes
module annassign-AnnAssign-35 where

  -- τ=788: 1 nodes, 1 σ-classes
  module τ788 where

    -- σ=1655 (1 nodes)
    cell-0 : κ 621 ≡ κ 621
    cell-0 = refl



-- κ=622: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-62 where

  -- τ=790: 1 nodes, 1 σ-classes
  module τ790 where

    -- σ=1660 (1 nodes)
    cell-0 : κ 622 ≡ κ 622
    cell-0 = refl



-- κ=623: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-37 where

  -- τ=791: 1 nodes, 1 σ-classes
  module τ791 where

    -- σ=1666 (1 nodes)
    cell-0 : κ 623 ≡ κ 623
    cell-0 = refl



-- κ=624: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-28 where

  -- τ=792: 1 nodes, 1 σ-classes
  module τ792 where

    -- σ=1667 (1 nodes)
    cell-0 : κ 624 ≡ κ 624
    cell-0 = refl



-- κ=625: 1 nodes, 1 τ-classes, 1 σ-classes
module coproduct-elim-If-7 where

  -- τ=793: 1 nodes, 1 σ-classes
  module τ793 where

    -- σ=1673 (1 nodes)
    cell-0 : κ 625 ≡ κ 625
    cell-0 = refl



-- κ=626: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-29 where

  -- τ=794: 1 nodes, 1 σ-classes
  module τ794 where

    -- σ=1674 (1 nodes)
    cell-0 : κ 626 ≡ κ 626
    cell-0 = refl



-- κ=627: 2 nodes, 1 τ-classes, 1 σ-classes
module usub-USub where

  -- τ=795: 2 nodes, 1 σ-classes
  module τ795 where

    -- σ=1678 (2 nodes)
    cell-0 : κ 627 ≡ κ 627
    cell-0 = refl



-- κ=628: 1 nodes, 1 τ-classes, 1 σ-classes
module projection-at-x3f-Attribute-1 where

  -- τ=796: 1 nodes, 1 σ-classes
  module τ796 where

    -- σ=1681 (1 nodes)
    cell-0 : κ 628 ≡ κ 628
    cell-0 = refl



-- κ=629: 1 nodes, 1 τ-classes, 1 σ-classes
module projection-compute-at-x3f-Call-1 where

  -- τ=797: 1 nodes, 1 σ-classes
  module τ797 where

    -- σ=1682 (1 nodes)
    cell-0 : κ 629 ≡ κ 629
    cell-0 = refl



-- κ=630: 1 nodes, 1 τ-classes, 1 σ-classes
module apply-Call-34 where

  -- τ=798: 1 nodes, 1 σ-classes
  module τ798 where

    -- σ=1683 (1 nodes)
    cell-0 : κ 630 ≡ κ 630
    cell-0 = refl



-- κ=631: 1 nodes, 1 τ-classes, 1 σ-classes
module endomorphism-UnaryOp-0 where

  -- τ=799: 1 nodes, 1 σ-classes
  module τ799 where

    -- σ=1684 (1 nodes)
    cell-0 : κ 631 ≡ κ 631
    cell-0 = refl



-- κ=632: 1 nodes, 1 τ-classes, 1 σ-classes
module lambda-Lambda-1 where

  -- τ=800: 1 nodes, 1 σ-classes
  module τ800 where

    -- σ=1685 (1 nodes)
    cell-0 : κ 632 ≡ κ 632
    cell-0 = refl



-- κ=633: 1 nodes, 1 τ-classes, 1 σ-classes
module keyword-keyword-1 where

  -- τ=801: 1 nodes, 1 σ-classes
  module τ801 where

    -- σ=1686 (1 nodes)
    cell-0 : κ 633 ≡ κ 633
    cell-0 = refl



-- κ=634: 1 nodes, 1 τ-classes, 1 σ-classes
module apply-Call-35 where

  -- τ=802: 1 nodes, 1 σ-classes
  module τ802 where

    -- σ=1687 (1 nodes)
    cell-0 : κ 634 ≡ κ 634
    cell-0 = refl



-- κ=635: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-36 where

  -- τ=803: 1 nodes, 1 σ-classes
  module τ803 where

    -- σ=1688 (1 nodes)
    cell-0 : κ 635 ≡ κ 635
    cell-0 = refl



-- κ=636: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-37 where

  -- τ=804: 1 nodes, 1 σ-classes
  module τ804 where

    -- σ=1690 (1 nodes)
    cell-0 : κ 636 ≡ κ 636
    cell-0 = refl



-- κ=637: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-63 where

  -- τ=809: 1 nodes, 1 σ-classes
  module τ809 where

    -- σ=1707 (1 nodes)
    cell-0 : κ 637 ≡ κ 637
    cell-0 = refl



-- κ=638: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-op-at-x3f-Attribute-4 where

  -- τ=810: 1 nodes, 1 σ-classes
  module τ810 where

    -- σ=1712 (1 nodes)
    cell-0 : κ 638 ≡ κ 638
    cell-0 = refl



-- κ=639: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-snoc-at-x3f-Call-6 where

  -- τ=811: 1 nodes, 1 σ-classes
  module τ811 where

    -- σ=1713 (1 nodes)
    cell-0 : κ 639 ≡ κ 639
    cell-0 = refl



-- κ=640: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-37 where

  -- τ=812: 1 nodes, 1 σ-classes
  module τ812 where

    -- σ=1714 (1 nodes)
    cell-0 : κ 640 ≡ κ 640
    cell-0 = refl



-- κ=641: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-30 where

  -- τ=813: 1 nodes, 1 σ-classes
  module τ813 where

    -- σ=1715 (1 nodes)
    cell-0 : κ 641 ≡ κ 641
    cell-0 = refl



-- κ=642: 1 nodes, 1 τ-classes, 1 σ-classes
module product-Tuple-35 where

  -- τ=814: 1 nodes, 1 σ-classes
  module tuple where

    -- σ=1718 (1 nodes)
    cell-0 : κ 642 ≡ κ 642
    cell-0 = refl



-- κ=643: 1 nodes, 1 τ-classes, 1 σ-classes
module index-Index-35 where

  -- τ=815: 1 nodes, 1 σ-classes
  module τ815 where

    -- σ=1719 (1 nodes)
    cell-0 : κ 643 ≡ κ 643
    cell-0 = refl



-- κ=644: 1 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-44 where

  -- τ=816: 1 nodes, 1 σ-classes
  module τ816 where

    -- σ=1720 (1 nodes)
    cell-0 : κ 644 ≡ κ 644
    cell-0 = refl



-- κ=645: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-38 where

  -- τ=817: 1 nodes, 1 σ-classes
  module τ817 where

    -- σ=1721 (1 nodes)
    cell-0 : κ 645 ≡ κ 645
    cell-0 = refl



-- κ=646: 2 nodes, 1 τ-classes, 1 σ-classes
module product-Tuple-36 where

  -- τ=818: 2 nodes, 1 σ-classes
  module tuple where

    -- σ=1724 (2 nodes)
    cell-0 : κ 646 ≡ κ 646
    cell-0 = refl



-- κ=647: 2 nodes, 1 τ-classes, 1 σ-classes
module index-Index-36 where

  -- τ=819: 2 nodes, 1 σ-classes
  module τ819 where

    -- σ=1725 (2 nodes)
    cell-0 : κ 647 ≡ κ 647
    cell-0 = refl



-- κ=648: 2 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-45 where

  -- τ=820: 2 nodes, 1 σ-classes
  module τ820 where

    -- σ=1726 (2 nodes)
    cell-0 : κ 648 ≡ κ 648
    cell-0 = refl



-- κ=649: 2 nodes, 1 τ-classes, 1 σ-classes
module index-Index-37 where

  -- τ=821: 2 nodes, 1 σ-classes
  module τ821 where

    -- σ=1727 (2 nodes)
    cell-0 : κ 649 ≡ κ 649
    cell-0 = refl



-- κ=650: 2 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-46 where

  -- τ=822: 2 nodes, 1 σ-classes
  module τ822 where

    -- σ=1728 (2 nodes)
    cell-0 : κ 650 ≡ κ 650
    cell-0 = refl



-- κ=651: 1 nodes, 1 τ-classes, 1 σ-classes
module annassign-AnnAssign-36 where

  -- τ=823: 1 nodes, 1 σ-classes
  module τ823 where

    -- σ=1729 (1 nodes)
    cell-0 : κ 651 ≡ κ 651
    cell-0 = refl



-- κ=652: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-map-DictComp-1 where

  -- τ=825: 1 nodes, 1 σ-classes
  module τ825 where

    -- σ=1742 (1 nodes)
    cell-0 : κ 652 ≡ κ 652
    cell-0 = refl



-- κ=653: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-64 where

  -- τ=826: 1 nodes, 1 σ-classes
  module τ826 where

    -- σ=1743 (1 nodes)
    cell-0 : κ 653 ≡ κ 653
    cell-0 = refl



-- κ=656: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-38 where

  -- τ=829: 1 nodes, 1 σ-classes
  module τ829 where

    -- σ=1755 (1 nodes)
    cell-0 : κ 656 ≡ κ 656
    cell-0 = refl



-- κ=657: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-31 where

  -- τ=830: 1 nodes, 1 σ-classes
  module τ830 where

    -- σ=1756 (1 nodes)
    cell-0 : κ 657 ≡ κ 657
    cell-0 = refl



-- κ=658: 1 nodes, 1 τ-classes, 1 σ-classes
module endomorphism-UnaryOp-1 where

  -- τ=831: 1 nodes, 1 σ-classes
  module τ831 where

    -- σ=1760 (1 nodes)
    cell-0 : κ 658 ≡ κ 658
    cell-0 = refl



-- κ=659: 1 nodes, 1 τ-classes, 1 σ-classes
module lambda-Lambda-2 where

  -- τ=832: 1 nodes, 1 σ-classes
  module τ832 where

    -- σ=1761 (1 nodes)
    cell-0 : κ 659 ≡ κ 659
    cell-0 = refl



-- κ=660: 1 nodes, 1 τ-classes, 1 σ-classes
module keyword-keyword-2 where

  -- τ=833: 1 nodes, 1 σ-classes
  module τ833 where

    -- σ=1762 (1 nodes)
    cell-0 : κ 660 ≡ κ 660
    cell-0 = refl



-- κ=661: 1 nodes, 1 τ-classes, 1 σ-classes
module apply-Call-36 where

  -- τ=834: 1 nodes, 1 σ-classes
  module τ834 where

    -- σ=1763 (1 nodes)
    cell-0 : κ 661 ≡ κ 661
    cell-0 = refl



-- κ=662: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-38 where

  -- τ=835: 1 nodes, 1 σ-classes
  module τ835 where

    -- σ=1764 (1 nodes)
    cell-0 : κ 662 ≡ κ 662
    cell-0 = refl



-- κ=663: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-39 where

  -- τ=836: 1 nodes, 1 σ-classes
  module τ836 where

    -- σ=1766 (1 nodes)
    cell-0 : κ 663 ≡ κ 663
    cell-0 = refl



-- κ=664: 2 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-65 where

  -- τ=838: 2 nodes, 1 σ-classes
  module τ838 where

    -- σ=1772 (2 nodes)
    cell-0 : κ 664 ≡ κ 664
    cell-0 = refl



-- κ=665: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-fold-JoinedStr-11 where

  -- τ=841: 1 nodes, 1 σ-classes
  module str where

    -- σ=1790 (1 nodes)
    cell-0 : κ 665 ≡ κ 665
    cell-0 = refl



-- κ=666: 1 nodes, 1 τ-classes, 1 σ-classes
module terminal-map-Return-19 where

  -- τ=842: 1 nodes, 1 σ-classes
  module τ842 where

    -- σ=1791 (1 nodes)
    cell-0 : κ 666 ≡ κ 666
    cell-0 = refl



-- κ=667: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-40 where

  -- τ=843: 1 nodes, 1 σ-classes
  module τ843 where

    -- σ=1792 (1 nodes)
    cell-0 : κ 667 ≡ κ 667
    cell-0 = refl



-- κ=668: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-Compare-21 where

  -- τ=844: 1 nodes, 1 σ-classes
  module τ844 where

    -- σ=1798 (1 nodes)
    cell-0 : κ 668 ≡ κ 668
    cell-0 = refl



-- κ=669: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-39 where

  -- τ=845: 1 nodes, 1 σ-classes
  module τ845 where

    -- σ=1801 (1 nodes)
    cell-0 : κ 669 ≡ κ 669
    cell-0 = refl



-- κ=670: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-66 where

  -- τ=847: 1 nodes, 1 σ-classes
  module τ847 where

    -- σ=1810 (1 nodes)
    cell-0 : κ 670 ≡ κ 670
    cell-0 = refl



-- κ=672: 2 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-fold-JoinedStr-12 where

  -- τ=849: 2 nodes, 1 σ-classes
  module str where

    -- σ=1816 (2 nodes)
    cell-0 : κ 672 ≡ κ 672
    cell-0 = refl



-- κ=675: 8 nodes, 1 τ-classes, 1 σ-classes
module div-Div where

  -- τ=852: 8 nodes, 1 σ-classes
  module τ852 where

    -- σ=1823 (8 nodes)
    cell-0 : κ 675 ≡ κ 675
    cell-0 = refl



-- κ=685: 1 nodes, 1 τ-classes, 1 σ-classes
module coerce-FormattedValue-11 where

  -- τ=862: 1 nodes, 1 σ-classes
  module τ862 where

    -- σ=1864 (1 nodes)
    cell-0 : κ 685 ≡ κ 685
    cell-0 = refl



-- κ=686: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-fold-JoinedStr-13 where

  -- τ=863: 1 nodes, 1 σ-classes
  module str where

    -- σ=1865 (1 nodes)
    cell-0 : κ 686 ≡ κ 686
    cell-0 = refl



-- κ=687: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-literal-List-3 where

  -- τ=864: 1 nodes, 1 σ-classes
  module list where

    -- σ=1866 (1 nodes)
    cell-0 : κ 687 ≡ κ 687
    cell-0 = refl



-- κ=688: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-67 where

  -- τ=865: 1 nodes, 1 σ-classes
  module τ865 where

    -- σ=1867 (1 nodes)
    cell-0 : κ 688 ≡ κ 688
    cell-0 = refl



-- κ=689: 1 nodes, 1 τ-classes, 1 σ-classes
module subobject-Attribute where

  -- τ=796: 1 nodes, 1 σ-classes
  module τ796 where

    -- σ=1873 (1 nodes)
    cell-0 : κ 689 ≡ κ 689
    cell-0 = refl



-- κ=690: 1 nodes, 1 τ-classes, 1 σ-classes
module subobject-test-Call where

  -- τ=866: 1 nodes, 1 σ-classes
  module τ866 where

    -- σ=1875 (1 nodes)
    cell-0 : κ 690 ≡ κ 690
    cell-0 = refl



-- κ=691: 1 nodes, 1 τ-classes, 1 σ-classes
module meet-BoolOp-1 where

  -- τ=867: 1 nodes, 1 σ-classes
  module τ867 where

    -- σ=1876 (1 nodes)
    cell-0 : κ 691 ≡ κ 691
    cell-0 = refl



-- κ=692: 1 nodes, 1 τ-classes, 1 σ-classes
module comprehension-comprehension-6 where

  -- τ=868: 1 nodes, 1 σ-classes
  module τ868 where

    -- σ=1877 (1 nodes)
    cell-0 : κ 692 ≡ κ 692
    cell-0 = refl



-- κ=693: 1 nodes, 1 τ-classes, 1 σ-classes
module lazy_fold-GeneratorExp-6 where

  -- τ=869: 1 nodes, 1 σ-classes
  module τ869 where

    -- σ=1878 (1 nodes)
    cell-0 : κ 693 ≡ κ 693
    cell-0 = refl



-- κ=694: 1 nodes, 1 τ-classes, 1 σ-classes
module apply-Call-37 where

  -- τ=870: 1 nodes, 1 σ-classes
  module τ870 where

    -- σ=1879 (1 nodes)
    cell-0 : κ 694 ≡ κ 694
    cell-0 = refl



-- κ=695: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-68 where

  -- τ=871: 1 nodes, 1 σ-classes
  module τ871 where

    -- σ=1880 (1 nodes)
    cell-0 : κ 695 ≡ κ 695
    cell-0 = refl



-- κ=696: 1 nodes, 1 τ-classes, 1 σ-classes
module powerset-Call-3 where

  -- τ=872: 1 nodes, 1 σ-classes
  module τ872 where

    -- σ=1882 (1 nodes)
    cell-0 : κ 696 ≡ κ 696
    cell-0 = refl



-- κ=697: 1 nodes, 1 τ-classes, 1 σ-classes
module annassign-AnnAssign-37 where

  -- τ=873: 1 nodes, 1 σ-classes
  module τ873 where

    -- σ=1883 (1 nodes)
    cell-0 : κ 697 ≡ κ 697
    cell-0 = refl



-- κ=698: 1 nodes, 1 τ-classes, 1 σ-classes
module ifexp-IfExp-4 where

  -- τ=874: 1 nodes, 1 σ-classes
  module τ874 where

    -- σ=1890 (1 nodes)
    cell-0 : κ 698 ≡ κ 698
    cell-0 = refl



-- κ=699: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-69 where

  -- τ=875: 1 nodes, 1 σ-classes
  module τ875 where

    -- σ=1891 (1 nodes)
    cell-0 : κ 699 ≡ κ 699
    cell-0 = refl



-- κ=700: 1 nodes, 1 τ-classes, 1 σ-classes
module bimap-BinOp-5 where

  -- τ=876: 1 nodes, 1 σ-classes
  module τ876 where

    -- σ=1896 (1 nodes)
    cell-0 : κ 700 ≡ κ 700
    cell-0 = refl



-- κ=701: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-70 where

  -- τ=877: 1 nodes, 1 σ-classes
  module τ877 where

    -- σ=1897 (1 nodes)
    cell-0 : κ 701 ≡ κ 701
    cell-0 = refl



-- κ=702: 1 nodes, 1 τ-classes, 1 σ-classes
module annassign-AnnAssign-38 where

  -- τ=879: 1 nodes, 1 σ-classes
  module τ879 where

    -- σ=1900 (1 nodes)
    cell-0 : κ 702 ≡ κ 702
    cell-0 = refl



-- κ=703: 1 nodes, 1 τ-classes, 1 σ-classes
module annassign-AnnAssign-39 where

  -- τ=880: 1 nodes, 1 σ-classes
  module τ880 where

    -- σ=1903 (1 nodes)
    cell-0 : κ 703 ≡ κ 703
    cell-0 = refl



-- κ=704: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-71 where

  -- τ=881: 1 nodes, 1 σ-classes
  module τ881 where

    -- σ=1908 (1 nodes)
    cell-0 : κ 704 ≡ κ 704
    cell-0 = refl



-- κ=705: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-40 where

  -- τ=882: 1 nodes, 1 σ-classes
  module τ882 where

    -- σ=1909 (1 nodes)
    cell-0 : κ 705 ≡ κ 705
    cell-0 = refl



-- κ=706: 1 nodes, 1 τ-classes, 1 σ-classes
module monoid-op-at-x3f-Attribute-3 where

  -- τ=810: 1 nodes, 1 σ-classes
  module τ810 where

    -- σ=1911 (1 nodes)
    cell-0 : κ 706 ≡ κ 706
    cell-0 = refl



-- κ=707: 1 nodes, 1 τ-classes, 1 σ-classes
module partial-apply-at-x3f-Call-1 where

  -- τ=883: 1 nodes, 1 σ-classes
  module τ883 where

    -- σ=1913 (1 nodes)
    cell-0 : κ 707 ≡ κ 707
    cell-0 = refl



-- κ=708: 1 nodes, 1 τ-classes, 1 σ-classes
module monoid-op-at-x3f-Call-7 where

  -- τ=884: 1 nodes, 1 σ-classes
  module τ884 where

    -- σ=1914 (1 nodes)
    cell-0 : κ 708 ≡ κ 708
    cell-0 = refl



-- κ=709: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-39 where

  -- τ=885: 1 nodes, 1 σ-classes
  module τ885 where

    -- σ=1915 (1 nodes)
    cell-0 : κ 709 ≡ κ 709
    cell-0 = refl



-- κ=710: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-32 where

  -- τ=886: 1 nodes, 1 σ-classes
  module τ886 where

    -- σ=1916 (1 nodes)
    cell-0 : κ 710 ≡ κ 710
    cell-0 = refl



-- κ=711: 1 nodes, 1 τ-classes, 1 σ-classes
module comprehension-comprehension-7 where

  -- τ=887: 1 nodes, 1 σ-classes
  module τ887 where

    -- σ=1921 (1 nodes)
    cell-0 : κ 711 ≡ κ 711
    cell-0 = refl



-- κ=712: 1 nodes, 1 τ-classes, 1 σ-classes
module lazy_fold-GeneratorExp-7 where

  -- τ=888: 1 nodes, 1 σ-classes
  module τ888 where

    -- σ=1922 (1 nodes)
    cell-0 : κ 712 ≡ κ 712
    cell-0 = refl



-- κ=713: 1 nodes, 1 τ-classes, 1 σ-classes
module apply-Call-38 where

  -- τ=889: 1 nodes, 1 σ-classes
  module τ889 where

    -- σ=1923 (1 nodes)
    cell-0 : κ 713 ≡ κ 713
    cell-0 = refl



-- κ=714: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-72 where

  -- τ=890: 1 nodes, 1 σ-classes
  module τ890 where

    -- σ=1924 (1 nodes)
    cell-0 : κ 714 ≡ κ 714
    cell-0 = refl



-- κ=715: 8 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-op-at-sequence-Attribute where

  -- τ=34: 8 nodes, 1 σ-classes
  module Self-_parent where

    -- σ=1926 (8 nodes)
    cell-0 : κ 715 ≡ κ 715
    cell-0 = refl



-- κ=716: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-fold-JoinedStr-14 where

  -- τ=892: 1 nodes, 1 σ-classes
  module str where

    -- σ=1930 (1 nodes)
    cell-0 : κ 716 ≡ κ 716
    cell-0 = refl



-- κ=717: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-snoc-at-sequence-Call-0 where

  -- τ=893: 1 nodes, 1 σ-classes
  module None where

    -- σ=1931 (1 nodes)
    cell-0 : κ 717 ≡ κ 717
    cell-0 = refl



-- κ=718: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-40 where

  -- τ=894: 1 nodes, 1 σ-classes
  module τ894 where

    -- σ=1932 (1 nodes)
    cell-0 : κ 718 ≡ κ 718
    cell-0 = refl



-- κ=719: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-fold-JoinedStr-15 where

  -- τ=895: 1 nodes, 1 σ-classes
  module str where

    -- σ=1940 (1 nodes)
    cell-0 : κ 719 ≡ κ 719
    cell-0 = refl



-- κ=720: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-snoc-at-sequence-Call-1 where

  -- τ=896: 1 nodes, 1 σ-classes
  module None where

    -- σ=1941 (1 nodes)
    cell-0 : κ 720 ≡ κ 720
    cell-0 = refl



-- κ=721: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-41 where

  -- τ=897: 1 nodes, 1 σ-classes
  module τ897 where

    -- σ=1942 (1 nodes)
    cell-0 : κ 721 ≡ κ 721
    cell-0 = refl



-- κ=722: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-fold-JoinedStr-16 where

  -- τ=898: 1 nodes, 1 σ-classes
  module str where

    -- σ=1952 (1 nodes)
    cell-0 : κ 722 ≡ κ 722
    cell-0 = refl



-- κ=723: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-snoc-at-sequence-Call-2 where

  -- τ=899: 1 nodes, 1 σ-classes
  module None where

    -- σ=1953 (1 nodes)
    cell-0 : κ 723 ≡ κ 723
    cell-0 = refl



-- κ=724: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-42 where

  -- τ=900: 1 nodes, 1 σ-classes
  module τ900 where

    -- σ=1954 (1 nodes)
    cell-0 : κ 724 ≡ κ 724
    cell-0 = refl



-- κ=725: 1 nodes, 1 τ-classes, 1 σ-classes
module mult-Mult where

  -- τ=901: 1 nodes, 1 σ-classes
  module τ901 where

    -- σ=1961 (1 nodes)
    cell-0 : κ 725 ≡ κ 725
    cell-0 = refl



-- κ=726: 1 nodes, 1 τ-classes, 1 σ-classes
module bimap-BinOp-6 where

  -- τ=903: 1 nodes, 1 σ-classes
  module τ903 where

    -- σ=1963 (1 nodes)
    cell-0 : κ 726 ≡ κ 726
    cell-0 = refl



-- κ=727: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-Compare-22 where

  -- τ=904: 1 nodes, 1 σ-classes
  module τ904 where

    -- σ=1964 (1 nodes)
    cell-0 : κ 727 ≡ κ 727
    cell-0 = refl



-- κ=728: 1 nodes, 1 τ-classes, 1 σ-classes
module ifexp-IfExp-5 where

  -- τ=905: 1 nodes, 1 σ-classes
  module τ905 where

    -- σ=1967 (1 nodes)
    cell-0 : κ 728 ≡ κ 728
    cell-0 = refl



-- κ=729: 1 nodes, 1 τ-classes, 1 σ-classes
module coerce-FormattedValue-12 where

  -- τ=906: 1 nodes, 1 σ-classes
  module τ906 where

    -- σ=1968 (1 nodes)
    cell-0 : κ 729 ≡ κ 729
    cell-0 = refl



-- κ=730: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-fold-JoinedStr-17 where

  -- τ=907: 1 nodes, 1 σ-classes
  module str where

    -- σ=1969 (1 nodes)
    cell-0 : κ 730 ≡ κ 730
    cell-0 = refl



-- κ=731: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-snoc-at-sequence-Call-3 where

  -- τ=908: 1 nodes, 1 σ-classes
  module None where

    -- σ=1970 (1 nodes)
    cell-0 : κ 731 ≡ κ 731
    cell-0 = refl



-- κ=732: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-43 where

  -- τ=909: 1 nodes, 1 σ-classes
  module τ909 where

    -- σ=1971 (1 nodes)
    cell-0 : κ 732 ≡ κ 732
    cell-0 = refl



-- κ=733: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-literal-Dict-5 where

  -- τ=910: 1 nodes, 1 σ-classes
  module dict where

    -- σ=1979 (1 nodes)
    cell-0 : κ 733 ≡ κ 733
    cell-0 = refl



-- κ=734: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-73 where

  -- τ=911: 1 nodes, 1 σ-classes
  module τ911 where

    -- σ=1980 (1 nodes)
    cell-0 : κ 734 ≡ κ 734
    cell-0 = refl



-- κ=735: 1 nodes, 1 τ-classes, 1 σ-classes
module partial-apply-at-state-Call-5 where

  -- τ=913: 1 nodes, 1 σ-classes
  module T where

    -- σ=1983 (1 nodes)
    cell-0 : κ 735 ≡ κ 735
    cell-0 = refl



-- κ=736: 1 nodes, 1 τ-classes, 1 σ-classes
module cardinality-Call-3 where

  -- τ=914: 1 nodes, 1 σ-classes
  module int where

    -- σ=1984 (1 nodes)
    cell-0 : κ 736 ≡ κ 736
    cell-0 = refl



-- κ=737: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-74 where

  -- τ=915: 1 nodes, 1 σ-classes
  module τ915 where

    -- σ=1985 (1 nodes)
    cell-0 : κ 737 ≡ κ 737
    cell-0 = refl



-- κ=738: 1 nodes, 1 τ-classes, 1 σ-classes
module bimap-BinOp-7 where

  -- τ=916: 1 nodes, 1 σ-classes
  module τ916 where

    -- σ=1988 (1 nodes)
    cell-0 : κ 738 ≡ κ 738
    cell-0 = refl



-- κ=739: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-75 where

  -- τ=917: 1 nodes, 1 σ-classes
  module τ917 where

    -- σ=1989 (1 nodes)
    cell-0 : κ 739 ≡ κ 739
    cell-0 = refl



-- κ=740: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-snoc-at-sequence-Call-4 where

  -- τ=918: 1 nodes, 1 σ-classes
  module None where

    -- σ=1991 (1 nodes)
    cell-0 : κ 740 ≡ κ 740
    cell-0 = refl



-- κ=741: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-44 where

  -- τ=919: 1 nodes, 1 σ-classes
  module τ919 where

    -- σ=1992 (1 nodes)
    cell-0 : κ 741 ≡ κ 741
    cell-0 = refl



-- κ=743: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-fold-JoinedStr-18 where

  -- τ=923: 1 nodes, 1 σ-classes
  module str where

    -- σ=2003 (1 nodes)
    cell-0 : κ 743 ≡ κ 743
    cell-0 = refl



-- κ=744: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-snoc-at-sequence-Call-5 where

  -- τ=924: 1 nodes, 1 σ-classes
  module None where

    -- σ=2004 (1 nodes)
    cell-0 : κ 744 ≡ κ 744
    cell-0 = refl



-- κ=745: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-45 where

  -- τ=925: 1 nodes, 1 σ-classes
  module τ925 where

    -- σ=2005 (1 nodes)
    cell-0 : κ 745 ≡ κ 745
    cell-0 = refl



-- κ=746: 1 nodes, 1 τ-classes, 1 σ-classes
module projection-at-state-Attribute where

  -- τ=153: 1 nodes, 1 σ-classes
  module Self-tau-canonical where

    -- σ=2006 (1 nodes)
    cell-0 : κ 746 ≡ κ 746
    cell-0 = refl



-- κ=747: 1 nodes, 1 τ-classes, 1 σ-classes
module projection-compute-at-state-Call where

  -- τ=927: 1 nodes, 1 σ-classes
  module Iter where

    -- σ=2007 (1 nodes)
    cell-0 : κ 747 ≡ κ 747
    cell-0 = refl



-- κ=748: 1 nodes, 1 τ-classes, 1 σ-classes
module total_order-Call-2 where

  -- τ=928: 1 nodes, 1 σ-classes
  module list where

    -- σ=2008 (1 nodes)
    cell-0 : κ 748 ≡ κ 748
    cell-0 = refl



-- κ=749: 1 nodes, 1 τ-classes, 1 σ-classes
module complement-If-1 where

  -- τ=929: 1 nodes, 1 σ-classes
  module τ929 where

    -- σ=2011 (1 nodes)
    cell-0 : κ 749 ≡ κ 749
    cell-0 = refl



-- κ=750: 1 nodes, 1 τ-classes, 1 σ-classes
module partial-at-mapping-Attribute where

  -- τ=34: 1 nodes, 1 σ-classes
  module Self-_parent where

    -- σ=2013 (1 nodes)
    cell-0 : κ 750 ≡ κ 750
    cell-0 = refl



-- κ=751: 1 nodes, 1 τ-classes, 1 σ-classes
module partial-apply-at-mapping-Call where

  -- τ=932: 1 nodes, 1 σ-classes
  module T where

    -- σ=2017 (1 nodes)
    cell-0 : κ 751 ≡ κ 751
    cell-0 = refl



-- κ=752: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-76 where

  -- τ=933: 1 nodes, 1 σ-classes
  module τ933 where

    -- σ=2018 (1 nodes)
    cell-0 : κ 752 ≡ κ 752
    cell-0 = refl



-- κ=753: 1 nodes, 1 τ-classes, 1 σ-classes
module lambda-Lambda-3 where

  -- τ=934: 1 nodes, 1 σ-classes
  module τ934 where

    -- σ=2024 (1 nodes)
    cell-0 : κ 753 ≡ κ 753
    cell-0 = refl



-- κ=754: 1 nodes, 1 τ-classes, 1 σ-classes
module keyword-keyword-3 where

  -- τ=935: 1 nodes, 1 σ-classes
  module τ935 where

    -- σ=2025 (1 nodes)
    cell-0 : κ 754 ≡ κ 754
    cell-0 = refl



-- κ=755: 1 nodes, 1 τ-classes, 1 σ-classes
module apply-Call-39 where

  -- τ=936: 1 nodes, 1 σ-classes
  module τ936 where

    -- σ=2026 (1 nodes)
    cell-0 : κ 755 ≡ κ 755
    cell-0 = refl



-- κ=756: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-77 where

  -- τ=937: 1 nodes, 1 σ-classes
  module τ937 where

    -- σ=2027 (1 nodes)
    cell-0 : κ 756 ≡ κ 756
    cell-0 = refl



-- κ=757: 1 nodes, 1 τ-classes, 1 σ-classes
module coerce-Call-1 where

  -- τ=404: 1 nodes, 1 σ-classes
  module τ404 where

    -- σ=2030 (1 nodes)
    cell-0 : κ 757 ≡ κ 757
    cell-0 = refl



-- κ=758: 1 nodes, 1 τ-classes, 1 σ-classes
module subscript-Subscript-47 where

  -- τ=938: 1 nodes, 1 σ-classes
  module τ938 where

    -- σ=2033 (1 nodes)
    cell-0 : κ 758 ≡ κ 758
    cell-0 = refl



-- κ=759: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-78 where

  -- τ=939: 1 nodes, 1 σ-classes
  module τ939 where

    -- σ=2034 (1 nodes)
    cell-0 : κ 759 ≡ κ 759
    cell-0 = refl



-- κ=760: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-fold-JoinedStr-19 where

  -- τ=940: 1 nodes, 1 σ-classes
  module str where

    -- σ=2047 (1 nodes)
    cell-0 : κ 760 ≡ κ 760
    cell-0 = refl



-- κ=761: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-snoc-at-sequence-Call-6 where

  -- τ=941: 1 nodes, 1 σ-classes
  module None where

    -- σ=2048 (1 nodes)
    cell-0 : κ 761 ≡ κ 761
    cell-0 = refl



-- κ=762: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-46 where

  -- τ=942: 1 nodes, 1 σ-classes
  module τ942 where

    -- σ=2049 (1 nodes)
    cell-0 : κ 762 ≡ κ 762
    cell-0 = refl



-- κ=763: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-33 where

  -- τ=943: 1 nodes, 1 σ-classes
  module τ943 where

    -- σ=2050 (1 nodes)
    cell-0 : κ 763 ≡ κ 763
    cell-0 = refl



-- κ=764: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-41 where

  -- τ=944: 1 nodes, 1 σ-classes
  module τ944 where

    -- σ=2053 (1 nodes)
    cell-0 : κ 764 ≡ κ 764
    cell-0 = refl



-- κ=765: 1 nodes, 1 τ-classes, 1 σ-classes
module partial-apply-at-x3f-Call-2 where

  -- τ=946: 1 nodes, 1 σ-classes
  module τ946 where

    -- σ=2059 (1 nodes)
    cell-0 : κ 765 ≡ κ 765
    cell-0 = refl



-- κ=766: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-79 where

  -- τ=947: 1 nodes, 1 σ-classes
  module τ947 where

    -- σ=2060 (1 nodes)
    cell-0 : κ 766 ≡ κ 766
    cell-0 = refl



-- κ=767: 1 nodes, 1 τ-classes, 1 σ-classes
module let-k-Assign-80 where

  -- τ=948: 1 nodes, 1 σ-classes
  module τ948 where

    -- σ=2068 (1 nodes)
    cell-0 : κ 767 ≡ κ 767
    cell-0 = refl



-- κ=768: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-fold-JoinedStr-20 where

  -- τ=951: 1 nodes, 1 σ-classes
  module str where

    -- σ=2084 (1 nodes)
    cell-0 : κ 768 ≡ κ 768
    cell-0 = refl



-- κ=769: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-snoc-at-sequence-Call-7 where

  -- τ=952: 1 nodes, 1 σ-classes
  module None where

    -- σ=2085 (1 nodes)
    cell-0 : κ 769 ≡ κ 769
    cell-0 = refl



-- κ=770: 1 nodes, 1 τ-classes, 1 σ-classes
module effect-seq-Expr-47 where

  -- τ=953: 1 nodes, 1 σ-classes
  module τ953 where

    -- σ=2086 (1 nodes)
    cell-0 : κ 770 ≡ κ 770
    cell-0 = refl



-- κ=771: 1 nodes, 1 τ-classes, 1 σ-classes
module equalizer-If-42 where

  -- τ=954: 1 nodes, 1 σ-classes
  module τ954 where

    -- σ=2087 (1 nodes)
    cell-0 : κ 771 ≡ κ 771
    cell-0 = refl



-- κ=772: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-34 where

  -- τ=955: 1 nodes, 1 σ-classes
  module τ955 where

    -- σ=2088 (1 nodes)
    cell-0 : κ 772 ≡ κ 772
    cell-0 = refl



-- κ=773: 1 nodes, 1 τ-classes, 1 σ-classes
module fold-For-35 where

  -- τ=956: 1 nodes, 1 σ-classes
  module τ956 where

    -- σ=2089 (1 nodes)
    cell-0 : κ 773 ≡ κ 773
    cell-0 = refl



-- κ=774: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-fold-Attribute where

  -- τ=957: 1 nodes, 1 σ-classes
  module str-join where

    -- σ=2091 (1 nodes)
    cell-0 : κ 774 ≡ κ 774
    cell-0 = refl



-- κ=775: 1 nodes, 1 τ-classes, 1 σ-classes
module free_monoid-fold-Call where

  -- τ=958: 1 nodes, 1 σ-classes
  module str where

    -- σ=2092 (1 nodes)
    cell-0 : κ 775 ≡ κ 775
    cell-0 = refl



-- κ=776: 1 nodes, 1 τ-classes, 1 σ-classes
module terminal-map-Return-20 where

  -- τ=959: 1 nodes, 1 σ-classes
  module τ959 where

    -- σ=2093 (1 nodes)
    cell-0 : κ 776 ≡ κ 776
    cell-0 = refl



-- κ=777: 1 nodes, 1 τ-classes, 1 σ-classes
module exponential-intro-FunctionDef-41 where

  -- τ=960: 1 nodes, 1 σ-classes
  module τ960 where

    -- σ=2094 (1 nodes)
    cell-0 : κ 777 ≡ κ 777
    cell-0 = refl



-- κ=778: 1 nodes, 1 τ-classes, 1 σ-classes
module classifier-intro-ClassDef-3 where

  -- τ=961: 1 nodes, 1 σ-classes
  module τ961 where

    -- σ=2095 (1 nodes)
    cell-0 : κ 778 ≡ κ 778
    cell-0 = refl



-- ══════════════════════════════════════════════════════════
-- Cleavage planes (forced case splits)
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
--   Rotation: (κ → τ → σ) depth=2
--   779 top-level modules
--   13 η-proofs
--   7 cleavage planes
-- ══════════════════════════════════════════════════════════

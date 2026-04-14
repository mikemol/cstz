"""GF(2)³ concrete model — the Fano base unit.

Paper Appendix E: "This appendix instantiates every definition,
proposition, and theorem using a single running example."

Population = integers 0-7 (their binary form IS the vector).
Discriminators = basis bitvectors e₁=4, e₂=2, e₃=1.
Evaluation = dot product (popcount parity of AND).

Mirrors: agda/CSTZ/Examples/GF2Cubed/*.agda
"""

from __future__ import annotations

from cstz.disc.gf2 import dot, basis

# ---------------------------------------------------------------------------
# Population: GF(2)³ = {0,...,7}
# ---------------------------------------------------------------------------

a0, a1, a2, a3 = 0b000, 0b001, 0b010, 0b011
a4, a5, a6, a7 = 0b100, 0b101, 0b110, 0b111

POPULATION = [a0, a1, a2, a3, a4, a5, a6, a7]

# ---------------------------------------------------------------------------
# Discriminator basis
# ---------------------------------------------------------------------------

e1 = basis(2)  # 0b100 = 4 — bit 2 (first bit in paper notation)
e2 = basis(1)  # 0b010 = 2 — bit 1
e3 = basis(0)  # 0b001 = 1 — bit 0

# Composites
e1_e2 = e1 ^ e2      # 0b110 = 6
e1_e3 = e1 ^ e3      # 0b101 = 5
e2_e3 = e2 ^ e3      # 0b011 = 3
e1_e2_e3 = e1 ^ e2 ^ e3  # 0b111 = 7 = a₇

# ---------------------------------------------------------------------------
# Evaluation = dot product
# ---------------------------------------------------------------------------

eval_dot = dot

# ---------------------------------------------------------------------------
# Regime stages
# ---------------------------------------------------------------------------

kappa_0 = []                # ∅
kappa_1 = [e1]              # ⟨e₁⟩
kappa_2 = [e1, e2]          # ⟨e₁, e₂⟩
kappa_3 = [e1, e2, e3]      # V

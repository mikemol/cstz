"""CSTZ Discrimination Framework — bitmask-tensor native implementation.

Parallel implementation of the paper "Discrimination as Foundation:
Set Theory from Exterior Algebra over GF(2)", derived from the Agda
formalization at agda/CSTZ/.

All representations are bitmask-native:
  - GF(2)^n vectors = packed int (n bits)
  - Exterior algebra = list[int] of length 2^n indexed by bitmask
  - Profiles/Ω = 2-bit packed int
  - Fano points = integers 1-7
"""

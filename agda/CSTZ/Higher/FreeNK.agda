------------------------------------------------------------------------
-- CSTZ.Higher.FreeNK
-- Paper §7, Thm 7.15: Free (n,k)-structure.  [A]
------------------------------------------------------------------------
module CSTZ.Higher.FreeNK where
-- S₃ symmetry provides directed structure at multiple levels
-- without constructing meta-regimes.  The number of directed
-- levels k is determined by the subgroup of S₃ employed.
-- For k > 3: iterate the triangle identity to a tower of nested
-- triangles.  Segal conditions hold: see Verification.Segal (B.37).

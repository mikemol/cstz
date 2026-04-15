# Potential conflicts / ambiguities

These are cases where the alignment committed a triple but the
second-best candidate scored nearly as high — either the aligner
picked wrong OR there is a genuine ambiguity (the paper states
the concept twice, or the Agda declaration bundles what the paper
splits).  Either case is worth investigating.

## Residues with tied top candidates

These are Agda decls that went to residue because no single paper
candidate dominated.  Listing the top-3 candidates lets reviewers
see whether the paper genuinely has redundant material or whether
one of the candidates is a better match than the aligner could tell.

| Agda | top-3 paper candidates |
|------|-------------------------|
| module:CSTZ.Category.Adjunction | definition:def:categ (1.64) / theorem:thm:adjuncti (1.64) |
| module:CSTZ.Category.Directed | definition:def:direc (1.64) / definition:def:categ (1.64) / definition:def:direc (1.64) |
| function:compose-witnesses | definition:def:categ (4.88) / definition:def:compo (4.88) |
| module:CSTZ.Category.Functor | definition:def:categ (1.64) / definition:def:funct (1.64) |
| module:CSTZ.Category.Limits | definition:def:categ (1.64) / proposition:prop:lim (1.64) |
| record:NatTrans | definition:def:nattr (3.69) / proposition:prop:nat (3.69) |
| function:interchange-at-F | remark:rem:interchan (1.64) / remark:rem:interchan (1.64) |
| module:CSTZ.Category.Yoneda | definition:def:categ (1.64) / theorem:thm:yoneda (1.64) |
| function:yoneda-faithful | theorem:thm:yoneda (5.33) / theorem:thm:ext (4.88) / remark:anon_006 (3.69) |
| function:retract-e₁ | theorem:thm:adjuncti (3.50) / theorem:thm:sheaf (3.50) |
| function:chain-cycle-indep | remark:rem:cycles (3.50) / remark:anon_033 (3.50) / corollary:cor:trunca (3.50) |
| function:profile-lin-check-2 | definition:def:profi (1.64) / definition:def:profi (1.64) |
| function:residue-a₀-a₂ | definition:def:resid (1.64) / remark:rem:residue-o (1.64) |

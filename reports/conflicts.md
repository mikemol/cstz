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
| module:CSTZ.Category.Adjunction | definition:def:categ (3.00) / theorem:thm:adjuncti (3.00) |
| data:Axis | corollary:cor:free-f (5.56) / theorem:prop:periodi (5.56) / theorem:thm:sheaf (4.00) |
| module:CSTZ.Category.Directed | definition:def:direc (3.00) / definition:def:categ (3.00) / definition:def:direc (3.00) |
| function:compose-witnesses | definition:def:categ (4.00) / definition:def:compo (4.00) |
| module:CSTZ.Category.Functor | definition:def:categ (3.00) / definition:def:funct (3.00) |
| module:CSTZ.Category.Limits | definition:def:categ (3.00) / proposition:prop:lim (3.00) |
| record:NatTrans | definition:def:nattr (5.56) / proposition:prop:nat (5.56) |
| function:interchange-at-F | remark:rem:interchan (3.00) / remark:rem:interchan (3.00) |
| module:CSTZ.Category.Yoneda | definition:def:categ (3.00) / theorem:thm:yoneda (3.00) |
| function:retract-e₁ | theorem:thm:adjuncti (5.27) / theorem:thm:sheaf (5.27) |
| function:chain-cycle-indep | remark:rem:cycles (5.27) / remark:anon_033 (5.27) / corollary:cor:trunca (5.27) |
| function:profile-lin-check-2 | definition:def:profi (3.00) / definition:def:profi (3.00) |
| function:residue-a₀-a₂ | definition:def:resid (3.00) / remark:rem:residue-o (3.00) |
| function:triangle-check | definition:def:trian (3.00) / remark:rem:triangle- (3.00) |

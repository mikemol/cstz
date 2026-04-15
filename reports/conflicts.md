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
| module:CSTZ.Axiom.Operationalist | definition:def:opera (5.68) / proposition:prop:inf (4.95) / theorem:thm:choice (4.95) |
| module:CSTZ.Category.Adjunction | definition:def:categ (0.73) / theorem:thm:adjuncti (0.73) |
| record:Adjunction | theorem:thm:adjuncti (3.64) / theorem:thm:sheaf (2.91) |
| module:CSTZ.Category.Directed | definition:def:direc (0.73) / definition:def:categ (0.73) / definition:def:direc (0.73) |
| function:compose-witnesses | definition:def:categ (4.95) / definition:def:compo (4.95) |
| module:CSTZ.Category.Functor | definition:def:categ (0.73) / definition:def:funct (0.73) |
| module:CSTZ.Category.Limits | definition:def:categ (0.73) / proposition:prop:lim (0.73) |
| record:NatTrans | definition:def:nattr (3.07) / proposition:prop:nat (3.07) |
| function:interchange-at-F | remark:rem:interchan (0.73) / remark:rem:interchan (0.73) |
| module:CSTZ.Category.Yoneda | definition:def:categ (0.73) / theorem:thm:yoneda (0.73) |
| function:retract-e₁ | theorem:thm:adjuncti (2.91) / theorem:thm:sheaf (2.91) |
| function:chain-cycle-indep | remark:rem:cycles (2.91) / remark:anon_033 (2.91) / corollary:cor:trunca (2.91) |
| function:profile-lin-check-2 | definition:def:profi (0.73) / definition:def:profi (0.73) |
| function:residue-a₀-a₂ | definition:def:resid (0.73) / remark:rem:residue-o (0.73) |
| function:triangle-check | definition:def:trian (0.73) / remark:rem:triangle- (0.73) |
| function:triangle-rot-σ | definition:def:tau-s (0.73) / definition:def:trian (0.73) / remark:rem:triangle- (0.73) |

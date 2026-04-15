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
| module:CSTZ.Axiom.Operationalist | definition:def:opera (5.40) / proposition:prop:inf (4.71) / theorem:thm:choice (4.71) |
| module:CSTZ.Category.Adjunction | definition:def:categ (0.69) / theorem:thm:adjuncti (0.69) |
| module:CSTZ.Category.Directed | definition:def:direc (0.69) / definition:def:categ (0.69) / definition:def:direc (0.69) |
| function:compose-witnesses | definition:def:categ (4.71) / definition:def:compo (4.71) |
| module:CSTZ.Category.Functor | definition:def:categ (0.69) / definition:def:funct (0.69) |
| module:CSTZ.Category.Limits | definition:def:categ (0.69) / proposition:prop:lim (0.69) |
| module:CSTZ.Category.NatTrans | definition:def:nattr (2.93) / proposition:prop:nat (2.93) / definition:def:categ (0.69) |
| record:NatTrans | definition:def:nattr (2.93) / proposition:prop:nat (2.93) |
| function:interchange-at-F | remark:rem:interchan (0.69) / remark:rem:interchan (0.69) |
| module:CSTZ.Category.Yoneda | theorem:thm:yoneda (3.62) / remark:anon_006 (2.93) / definition:def:categ (0.69) |
| function:profile-lin-check-2 | definition:def:profi (0.69) / definition:def:profi (0.69) |
| function:residue-a₀-a₂ | definition:def:resid (0.69) / remark:rem:residue-o (0.69) |
| function:triangle-check | definition:def:trian (0.69) / remark:rem:triangle- (0.69) |
| function:triangle-rot-σ | definition:def:tau-s (0.69) / definition:def:trian (0.69) / remark:rem:triangle- (0.69) |
| function:triangle-rot-τ | definition:def:tau-s (0.69) / definition:def:trian (0.69) / remark:rem:triangle- (0.69) |

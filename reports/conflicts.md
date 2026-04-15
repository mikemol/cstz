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
| module:CSTZ.All | definition:def:repre (0.32) / definition:def:power (0.31) / proposition:prop:gro (0.31) |
| module:CSTZ.Axiom.EvalLinearity | definition:def:eval (0.45) / definition:def:eval- (0.44) / remark:anon_053 (0.31) |
| module:CSTZ.Axiom.ProfileLinearity | definition:def:profi (0.48) / definition:def:profi (0.44) / definition:def:cover (0.34) |
| record:NatTrans | definition:def:funct (0.47) / proposition:prop:nat (0.45) |
| function:retract-e₁ | theorem:thm:sheaf (0.40) / definition:def:eval (0.40) / theorem:thm:adjuncti (0.40) |
| function:profile-lin-check-1 | definition:def:profi (0.59) / definition:def:profi (0.57) / definition:def:eval- (0.55) |
| function:profile-lin-check-2 | definition:def:profi (0.59) / definition:def:profi (0.57) / definition:def:eval- (0.55) |
| function:residue-a₀-a₂ | definition:def:resid (0.60) / remark:rem:residue-o (0.57) / definition:anon_013 (0.46) |
| function:resolve-a₀-a₂ | proposition:prop:pre (0.41) / remark:anon_097 (0.39) / definition:def:eval (0.39) |
| function:resolve-a₀-a₂' | proposition:prop:pre (0.41) / remark:anon_097 (0.39) / definition:def:eval (0.39) |
| module:CSTZ.Examples.GF2Cubed.Higher | corollary:cor:free-d (0.31) / remark:rem:2cat (0.28) / remark:anon_045 (0.28) |
| function:self-inverse-e₁e₂ | corollary:cor:self-m (0.65) / theorem:thm:self-enr (0.61) / theorem:thm:self-hos (0.59) |
| function:triangle-rot-σ | definition:def:trian (0.59) / definition:def:tau-s (0.59) / remark:rem:triangle- (0.56) |
| function:triangle-rot-τ | definition:def:trian (0.59) / definition:def:tau-s (0.59) / remark:rem:triangle- (0.56) |
| function:g0-basis | definition:def:bound (0.36) / proposition:prop:for (0.34) |
| function:g0-grade | remark:anon_099 (0.40) / proposition:prop:gro (0.40) / definition:def:degen (0.39) |
| function:g2-e₁e₂-grade | remark:anon_099 (0.41) / proposition:prop:gro (0.40) / definition:def:degen (0.39) |
| function:g2-e₁e₃-grade | remark:anon_099 (0.41) / proposition:prop:gro (0.40) / definition:def:degen (0.39) |
| function:g2-e₂e₃-grade | remark:anon_099 (0.41) / proposition:prop:gro (0.40) / definition:def:degen (0.39) |
| function:g3-top-grade | remark:anon_099 (0.40) / proposition:prop:gro (0.40) / definition:def:degen (0.39) |
| function:dd-explicit | corollary:anon_038 (0.48) / remark:anon_006 (0.44) / remark:anon_127 (0.41) |
| function:comm-subset | proposition:prop:for (0.48) / proposition:prop:nat (0.40) |
| function:univ-separated | proposition:prop:pai (0.39) / definition:def:eval (0.39) / definition:def:eval- (0.34) |
| function:univ-separated' | proposition:prop:pai (0.39) / definition:def:eval (0.39) / definition:def:eval- (0.34) |

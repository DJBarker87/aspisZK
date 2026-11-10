-- PCVL_ carrier map for the fresh VTop emission (inputs/vtop_prelude.lean).
-- Texts equal to the gate type declarations (checked by eye against Stage2ContinuationTypes lines 192-203): alias to the gate constants.
abbrev verifier.Reader := AspisR1Stage2.verifier.Reader
abbrev verifier.resume.closure (H : Type) := AspisR1Stage2.verifier.resume.closure H
abbrev verifier.resume.closure_1 (H : Type) := AspisR1Stage2.verifier.resume.closure_1 H
-- aspis_core.r0.Error has no gate counterpart (the gate treats resume as Ops field op18); fresh declaration kept as is (registration attributes stripped).
inductive aspis_core.r0.Error where
| IndexOutOfRange : aspis_core.r0.Error
| WrongLength : aspis_core.r0.Error
| ZeroDenominator : aspis_core.r0.Error
| Allocation : aspis_core.r0.Error
| NonCanonical : aspis_core.r0.Error
| WrongField : aspis_core.r0.Error
| InvalidPoints : aspis_core.r0.Error
| QuotientNotInImage : aspis_core.r0.Error
| RankDeficient : aspis_core.r0.Error
| Parse : aspis_core.r0.Error
| Semantic : aspis_core.r0.Error
| Schedule : aspis_core.r0.Error
| Sampler : aspis_core.r0.Error
| Commitment : aspis_core.r0.Error
| Authentication : aspis_core.r0.Error
| V1 : aspis_core.r0.Error
| V2 : aspis_core.r0.Error

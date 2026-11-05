# NIT callee/stub interpretation table

All uses retain P6/D188 option A (reclassification, no trust row added/removed). Caller arguments are the SAME model values carried in each cut. No new native multiplication is run.

| Native logged call | Paired Lean theorem | Domain proved at caller |
|---|---|---|
| NIG Common::qm | NIT_FieldInterpretation.qm, instantiated by NIT_CommonChain.local_log/complete | Canonical SAME factor rows from NEW/NIG_PairInputs.new_owner |
| NIG Low::emul | NIT_FieldInterpretation.em, NIT_LowChain.local_log/complete | Canonical SAME powers4 from NFW_PowersCohort.source |
| NIG Low::square | NHX_LowScale.square | Exactly QUARTER, QUARTER |
| NIG Low::scale | NIT_LowInterpretation.scale / NHX_LowScale.total | Exact scalar 134217728, SAME product; all raw input words admitted by scale law |
| NIG Final::final_mul/final_add | NIT_FieldInterpretation.em/ea; NIT_FinalCompleteness.complete | Canonical SAME parts/powers7/sum invariant |
| NIG Libra::libra_field/mul/add | NHE_FieldPort.adopted, NHE_FieldCanonical.success, NIT_FieldInterpretation.em/ea; NIT_LibraInterpretation | SAME f2048/j<4; full field Result, canonical returning coefficient and libra/parts invariant |
| NIT Tail::group | NHX_GroupPacket.source/output | SAME S2 w, f2048, SAME canonical low16 from NIT_LowChain.complete; byte windows retained from NIQ_FieldDomains.final |
| NIT Tail::factored | NHX_FactoredPacket.source | SAME canonical ap0/ap1 and copied canonical w.extra from NEW/NIG_PairInputs.new_owner |

The new Kani stubs are explicit local-record calls, not kani multiplication replacements or function contracts. LPh-style interpretation laws above are instantiated by the per-cut Lean chains; no unpaired arithmetic stub is credited. Full parent pair/finish composition is still OPEN.

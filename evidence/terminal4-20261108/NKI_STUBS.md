# NKI stubs

All native field operations remain opaque. No field multiplication is proved in Kani.

| Native stub | Paired Lean theorem | Domain / exact result |
|---|---|---|
|NKI_new|NJB_PreparedLaws.new_result|Canon high; complete9word prepared cache, Domain cache high|
|NKI_empty|JGa_EmptyRoot.source|actual level<20; exact canonical8word empty digest|
|NKI_tweak|NKI_TweakScalar.source|expectedWord<P, actual1095962629; M31.add ok exact natural sum%P|
|NKI_lift|FIw_ScalarArithmetic.lift_run/lift_value|actual targetWord<P; exact lifted QM31|
|NKI_sub|NJB_StubLaws.qm_sub|both actual operands Canon; exact field difference|
|NKI_pack|NJB_PackLaw.result|all4actual residuals Canon; complete packed QM31|
|NKI_mul|NJB_PreparedLaws.mul_result|same constructor cache Domain and canonical packed argument; exact field product|

NKI_AppendPacket derives every domain internally at SAME decoded arguments. Child domains are never root hypotheses beyond canonical actual inputs and level<20. Full output includes both2cell channels, including ZERO inactive channel. Native235 inherited stubs: concrete234 SAME arguments, four QM31.add via NJX_AppendFold.step_source/NJB_StubLaws.qm_add, all Canon; complete4cell frame.

Inherited260/233kind10 stubs NJX_e_m31/NKI_rmul are paired with new NKI_ScalarStubLaw.source L054: full emitted QM31.mul_m31 returns ok canonical with decode=decode x*(s.val:K), all typed x/s; reuses JFy_PreparedSteps.scalar plus FIw_ScalarArithmetic.mul/probe mapping. NKI_row is paired with NIH_SelectorRow.result on SAME full selectors/row<1024; canonical high64/low16 supplied. NKI_reconstruct is paired with JGa_Reconstruct.source and NHG_ExtraLeaves.reconstruct_result/reconstruct_step (CLOSED257) on SAME canonical16view. NKI_renter kind1/2 uses NJB_StubLaws.qm_add/qm_sub. NKI_sum uses NHG_ExtraLeaves.sum_result at exactranges4..25/33..57; receiver arbitrary-window frame NKI_SelectorWindow.source. Every inherited prepared operation uses NJB_PreparedLaws.new_result/mul_result, with NKI_InitialDomains.source deriving SAME cache domains.


233 scaling by1024/1048576 uses NKI_ScalarStubLaw.source at the actual canonical reconstructed QM31. NKI_ValueRoot derives canonicality from JGa_Reconstruct and emitted range/cohort association; tails30..32 are framed, not replaced by arbitrary values. Low-mix251support uses the SAME complete prepared caches and NJB_PreparedLaws.mul_result, NJB_StubLaws.qm_add/qm_sub and FIw_ScalarArithmetic.lift_run/lift_value on actual low0/11/12. NKI_LowMixCaller derives domains; no new native field multiplication or unsupported opaque reply is credited.


| Additional call-log reply | Named law / CLOSED child | Actual domain |
|---|---|---|
|NJX prologue/write kind0 direct QM31.mul|NJB_StubLaws.qm_mul|Both SAME operands Canon, derived in NKI_InitialTrace.Canonical; emitted ok result decodes to product|
|NKI_sadd, NKI_renter kind1/2|NJB_StubLaws.qm_add/qm_sub|Both SAME actual operands Canon; exact emitted addition/subtraction result|
|NKI_low_new / NKI_low_mul / NKI_low_add|NJB_PreparedLaws.new_result / mul_result / NJB_StubLaws.qm_add|SAME actual low, complete cache, canonical local/output; NKI_LowMix derives each successive domain|
|NKI_reconstruct|NHG_ExtraLeaves.reconstruct_result and reconstruct_step (CLOSED257), JGa_Reconstruct.source|SAME actual canonical16opening view; exact emitted reconstruct result and canonicality|
|NKI_sum / inherited NJX sum_high|NHG_ExtraLeaves.sum_result (CLOSED262)|SAME canonical high64/low16 and exact two ranges; full receiver association supplied by NKI_SelectorWindow|

No square is introduced in the four candidate root call graphs. Inherited square support, if used by a later parent, requires RPv_JFy_SquareTotal.source at its actual canonical operand; it earns no parent credit here. The direct QM31.mul law above is Lean-only: native kind0 records the call and reply, never runs multiplication.

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

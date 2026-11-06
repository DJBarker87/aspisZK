# NJL stub register

No new arithmetic, copy, function-contract or runtime-value stub. Exact KMX patch SHA256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67; native controls use its original copy_nonoverlapping stub and matched controls. No Option<fn>, writable static, proof_for_contract or stub_verified.

| Reused oracle | Paired emitted Lean law | Domain established internally |
|---|---|---|
| NJB_Ops::NJB_add (active, pattern, scales) | NJB_StubLaws.qm_add | both SAME operands Canon; intermediate replies canonical from previous law |
| NJB_Ops::NJB_mul | NJB_StubLaws.qm_mul | both SAME operands Canon; no native multiplication |
| NJB_new | NJB_PreparedLaws.new_result | SAME canonical multiplier from actual preceding field Result |
| NJB_PreparedOps::NJB_mul | NJB_PreparedLaws.mul_result | SAME PreparedFor cache from constructor, canonical opened word |

Active pairing is explicit in NJL_LowDischarge.Clauses and NJL_ActiveInvocation.HighStep. Prepared pairing is explicit in NJL_AbsorptionPrologue.Clauses. Canonical unused reply slots use the proved ZERO, never a stronger caller precondition.

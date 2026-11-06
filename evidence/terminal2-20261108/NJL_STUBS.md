# NJL stub register

No new arithmetic, copy, function-contract or runtime-value stub. Exact KMX patch SHA256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67; native controls use its original copy_nonoverlapping stub and matched controls. No Option<fn>, writable static, proof_for_contract or stub_verified.

| Reused oracle | Paired emitted Lean law | Domain established internally |
|---|---|---|
| NJB_Ops::NJB_add (active, pattern, scales) | NJB_StubLaws.qm_add | both SAME operands Canon; intermediate replies canonical from previous law |
| NJB_Ops::NJB_mul | NJB_StubLaws.qm_mul | both SAME operands Canon; no native multiplication |
| NJB_new | NJB_PreparedLaws.new_result | SAME canonical multiplier from actual preceding field Result |
| NJB_PreparedOps::NJB_mul | NJB_PreparedLaws.mul_result | SAME PreparedFor cache from constructor, canonical opened word |

Active pairing is explicit in NJL_LowDischarge.Clauses and NJL_ActiveInvocation.HighStep. Prepared pairing is explicit in NJL_AbsorptionPrologue.Clauses. Canonical unused reply slots use the proved ZERO, never a stronger caller precondition.

## Additional explicit pairings

| Oracle/window | Named Lean value/domain law | Scope |
|---|---|---|
| NJL_add inside endpoint one-write | NJB_StubLaws.qm_add; NJL_EndpointCell.source | SAME canonical left/rhs; actual reply canonical; kind1 now explicitly observed K015/016 |
| selected_binary_ref concrete erased Copy | NIH_SelectedBinary.result instantiated in NJL_EndpointRoot.selected_value | SAME canonical high, weight≤1; caller_weight derives bound for every actual genuine link |
| NJL_lane_oracle inside std from_fn | NJB_AbsorptionLane.result, composed in NJL_AbsorptionInvocation.lanes | Structural constructor window only: lane/reply preserved; actual callback arguments/cache domain supplied by NJB_K046/047 and the SAME source closure |
| NJB_occupancy/path field/prepared logging operations | NJB_StubLaws.qm_add/qm_sub/qm_mul; NJB_PreparedLaws.new_result/mul_result | Explicit Clauses/Step fields in NJL occupancy/path packets; canonical intermediate operands/cache domains all derived |
| native loop control recording bodies | No arithmetic value credit | Original body arithmetic erased only for control/count; separate arbitrary-prestate value windows and Lean induction supply all values |

The obsolete scan-based lookup expected function receives no final row authority: K019/020 uses direct pinned literal expected arrays, represented with the same decimal payloads in Lean. No new Rust reference-loop interpretation or extraction is relied on.

## Stage8 paired integer/reduction clauses
|Native local operation|Full Lean Result/value/domain law|Caller proof|
|---|---|---|
|NJB_product (U64 multiply)|NJL_TagWords.product, NJB_TagRaw.product; operands<P, exact natural product≤B|NJL_TagWords.domain, exact same high-block/limb and registry tag|
|raw checked add|NJL_TagRawStep.add; raw≤kB,k<4,product≤B; full Result and exact natural sum|NJL_TagRawTrace.source|
|reduce_u64/add M31|NJB_TagReduce.reduce/add/result; every rawU64, old<P, residue<P|NJL_TagReduction.step_source/source and outer canonical invariant|
|216 child in217|NJL_TagRoot.source, SAME high selectors canonical, coordinate<30|NJL_TagForward.source internally applies child|
No field multiplication in Kani. Integer multiplies are opaque natural-value replies paired above; source integer overflow safety is proved symbolically. No contracts or function pointers.

## Stage9 shared selector
Pack reply paired with NJB_PackLaw.result (CLOSED NFT_Pack.source), exact same gathered4cells canonical by lanes_canonical. Product/add reply paired NJB_StubLaws.qm_mul/qm_add; domains supplied from same input selector, pack Result, and evolving24state. NJL_SharedRoot.source constructs actual33selector products for adopted NHU_Preweighted.result; its positive/interval/canonical domains are discharged internally at N33/start49. Native pack is opaque, never field multiplication in Kani.

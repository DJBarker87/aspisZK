import R1Z.PV_RunJoin_InputRelation31
import R1Z.PV_RunJoin_CanonicalHonesty30
import R1Z.PV_RunJoin_RuntimeRejections30
import R1Z.PV_RunJoin_OuterCommonFacts30
import R1Z.PV_RunJoin_LaneABI31
import R1Z.PV_RunJoin_OuterChecked30
import R1Z.PV_RunJoin_CodecOuter30
import R1Z.PV_RunJoin_DecodedFrontier29
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CanonicalInput31
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30 R0Z.WriterRefine
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
local instance : LaneRoot := PV_RunJoin_LaneABI31.native
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]


theorem transfer (bytes : Slice U8) (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestPrivateTransferWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : PV_RunJoin_CodecOuter30.Snapshot)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : PV_RunJoin_CodecOuter30.run bytes
      (pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1 p w context) = ok (.Ok (snapshot,c))) :
    ∃ root, pool_v1.pair_forest_trace.lane_root w.input.pair = ok (.Ok root) ∧
      PV_RunJoin_InputRelation31.Relation (K := K)
        (PV_RunJoin_OuterChecked30.transferInput p w root (PV_RunJoin_CodecOuter30.snapshot snapshot) c) := by
  obtain ⟨root,hr,hs,hc,hf⟩ := PV_RunJoin_CanonicalHonesty30.transfer_payload bytes p w context snapshot c h
  obtain ⟨_,compiled⟩ := PV_RunJoin_CodecOuter30.returned bytes _ snapshot c h
  obtain ⟨_,_,_,runtime⟩ := PV_RunJoin_OuterPrefix30.transfer p w context _ c compiled
  have admission := PV_RunJoin_OuterCommonFacts30.common_return _ _ _ _ _ _ _ _ runtime
  have clauses := (PV_RunJoin_RuntimeRejections30.success_iff _ _ _ _ _ _ _ _).mp admission
  refine ⟨root,hr,?_⟩
  apply PV_RunJoin_InputRelation31.relation _ hs hc hf
  exact clauses.2.2.2.2
#print axioms transfer

theorem withdrawal (bytes : Slice U8) (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestWithdrawalWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : PV_RunJoin_CodecOuter30.Snapshot)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : PV_RunJoin_CodecOuter30.run bytes
      (pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1 p w context) = ok (.Ok (snapshot,c))) :
    ∃ root, pool_v1.pair_forest_trace.lane_root w.input.pair = ok (.Ok root) ∧
      PV_RunJoin_InputRelation31.Relation (K := K)
        (PV_RunJoin_OuterChecked30.withdrawalInput p w root (PV_RunJoin_CodecOuter30.snapshot snapshot) c) := by
  obtain ⟨root,hr,hs,hc,hf⟩ := PV_RunJoin_CanonicalHonesty30.withdrawal_payload bytes p w context snapshot c h
  obtain ⟨_,compiled⟩ := PV_RunJoin_CodecOuter30.returned bytes _ snapshot c h
  obtain ⟨_,_,_,runtime⟩ := PV_RunJoin_OuterPrefix30.withdrawal p w context _ c compiled
  have admission := PV_RunJoin_OuterCommonFacts30.common_return _ _ _ _ _ _ _ _ runtime
  have clauses := (PV_RunJoin_RuntimeRejections30.success_iff _ _ _ _ _ _ _ _).mp admission
  refine ⟨root,hr,?_⟩
  apply PV_RunJoin_InputRelation31.relation _ hs hc hf
  exact clauses.2.2.2.2
#print axioms withdrawal

end R1Z.PV_RunJoin_CanonicalInput31

import R1Z.PV_RunJoin_HonestPackage31
import R1Z.PV_RunJoin_CanonicalInput31
import R1Z.PV_RunJoin_SemanticRecipient31
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CanonicalHonest31
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30 R0Z.WriterRefine
open PV_RunJoin_SemanticChange30
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
      PV_RunJoin_ConsumerBoundary25.HonestInput (K := K)
        (PV_RunJoin_OuterChecked30.transferInput p w root (PV_RunJoin_CodecOuter30.snapshot snapshot) c) := by
  obtain ⟨root,hr,hs,hc,hf⟩ := PV_RunJoin_CanonicalHonesty30.transfer_payload bytes p w context snapshot c h
  obtain ⟨other,ho,hin⟩ := PV_RunJoin_CanonicalInput31.transfer (K := K) bytes p w context snapshot c h
  have he := core.result.Result.Ok.inj (Result.ok.inj (hr.symm.trans ho))
  cases he
  obtain ⟨_,compiled⟩ := PV_RunJoin_CodecOuter30.returned bytes _ snapshot c h
  have hsum := PV_RunJoin_OuterConservation30.transfer p w context _ c compiled
  refine ⟨root,hr,?_⟩
  apply PV_RunJoin_HonestPackage31.honest _ hs hc hf
  · exact PV_RunJoin_SemanticOptions30.transfer_shape p w root _ c
  · exact hsum.2.2.2.2
  · exact hin
  · exact PV_RunJoin_SemanticRecipient31.recipient _ hs hc hf rfl
#print axioms transfer

theorem withdrawal (bytes : Slice U8) (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestWithdrawalWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : PV_RunJoin_CodecOuter30.Snapshot)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : PV_RunJoin_CodecOuter30.run bytes
      (pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1 p w context) = ok (.Ok (snapshot,c))) :
    ∃ root, pool_v1.pair_forest_trace.lane_root w.input.pair = ok (.Ok root) ∧
      PV_RunJoin_ConsumerBoundary25.HonestInput (K := K)
        (PV_RunJoin_OuterChecked30.withdrawalInput p w root (PV_RunJoin_CodecOuter30.snapshot snapshot) c) := by
  obtain ⟨root,hr,hs,hc,hf⟩ := PV_RunJoin_CanonicalHonesty30.withdrawal_payload bytes p w context snapshot c h
  obtain ⟨other,ho,hin⟩ := PV_RunJoin_CanonicalInput31.withdrawal (K := K) bytes p w context snapshot c h
  have he := core.result.Result.Ok.inj (Result.ok.inj (hr.symm.trans ho))
  cases he
  obtain ⟨_,compiled⟩ := PV_RunJoin_CodecOuter30.returned bytes _ snapshot c h
  have hsum := PV_RunJoin_OuterConservation30.withdrawal p w context _ c compiled
  refine ⟨root,hr,?_⟩
  apply PV_RunJoin_HonestPackage31.honest _ hs hc hf
  · exact PV_RunJoin_SemanticOptions30.withdrawal_shape p w context root _ c compiled
  · exact hsum.2.2
  · exact hin
  · exact PV_RunJoin_SemanticOptions30.withdrawal_variant p w context root _ c compiled
#print axioms withdrawal
end R1Z.PV_RunJoin_CanonicalHonest31

import R1Z.PV_RunJoin_LaneRootField31
import R1Z.PV_RunJoin_CanonicalHonesty30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LaneCanonical31
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30 R0Z.WriterRefine
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_Src_ExternalReference.dictionary
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
local instance : LaneRoot := PV_RunJoin_LaneABI31.native
variable {K : Type} [Field K] [CharP K 2147483647]

theorem transfer_root (bytes : Slice U8)
    (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestPrivateTransferWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : PV_RunJoin_CodecOuter30.Snapshot)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : PV_RunJoin_CodecOuter30.run bytes
      (pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1 p w context) = ok (.Ok (snapshot,c))) :
    ∃ root, pool_v1.pair_forest_trace.lane_root w.input.pair = ok (.Ok root) ∧
      Canon8 root ∧ digK (K := K) root = PV_RunJoin_LaneRootField31.meaning w.input.pair := by
  obtain ⟨_,compiled⟩ := PV_RunJoin_CodecOuter30.returned bytes _ snapshot c h
  have common := PV_RunJoin_OuterCommonFacts30.transfer p w context _ c compiled
  obtain ⟨root,hr,_,_,_⟩ := PV_RunJoin_CanonicalHonesty30.transfer_payload bytes p w context snapshot c h
  have hcall : PV_RunJoin_LaneABI31.call w.input.pair = ok (.Ok root) := hr
  obtain ⟨hc,hm⟩ := PV_RunJoin_LaneRootField31.successful_root (K := K) _ _ hcall common.membership
  exact ⟨root,hr,hc,hm⟩
#print axioms transfer_root

theorem withdrawal_root (bytes : Slice U8)
    (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestWithdrawalWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : PV_RunJoin_CodecOuter30.Snapshot)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : PV_RunJoin_CodecOuter30.run bytes
      (pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1 p w context) = ok (.Ok (snapshot,c))) :
    ∃ root, pool_v1.pair_forest_trace.lane_root w.input.pair = ok (.Ok root) ∧
      Canon8 root ∧ digK (K := K) root = PV_RunJoin_LaneRootField31.meaning w.input.pair := by
  obtain ⟨_,compiled⟩ := PV_RunJoin_CodecOuter30.returned bytes _ snapshot c h
  have common := PV_RunJoin_OuterCommonFacts30.withdrawal p w context _ c compiled
  obtain ⟨root,hr,_,_,_⟩ := PV_RunJoin_CanonicalHonesty30.withdrawal_payload bytes p w context snapshot c h
  have hcall : PV_RunJoin_LaneABI31.call w.input.pair = ok (.Ok root) := hr
  obtain ⟨hc,hm⟩ := PV_RunJoin_LaneRootField31.successful_root (K := K) _ _ hcall common.membership
  exact ⟨root,hr,hc,hm⟩
#print axioms withdrawal_root
end R1Z.PV_RunJoin_LaneCanonical31

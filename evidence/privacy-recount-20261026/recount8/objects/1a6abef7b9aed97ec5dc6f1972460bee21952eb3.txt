import R1Z.PV_RunJoin_OuterCommonFacts30
import R1Z.PV_RunJoin_RuntimeRejections30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PreparationContext32
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30
variable [LaneRoot] [BuilderForestAdmissionPort.ExternalLinear] [BuilderForestAdmissionPort.Records]

/-- The frozen wrapper validates these original context coordinates after
replacing the lane-root coordinate. No equation for the overwritten root is
assumed or inferred. -/
theorem transfer_binding
    (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestPrivateTransferWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1 p w context snapshot = ok (.Ok c)) :
    context.runtime_binding.pool=p.pool ∧
    context.runtime_binding.deployment_domain=p.deployment_domain ∧
    context.runtime_binding.anchor_sequence=p.anchor_sequence ∧
    context.runtime_binding.asset_id=p.asset_id := by
  obtain ⟨root,_,_,hc⟩ := PV_RunJoin_OuterPrefix30.transfer p w context snapshot c h
  have common := PV_RunJoin_OuterCommonFacts30.common_return _ _ _ _ _ _ _ _ hc
  have runtime := ((PV_RunJoin_RuntimeRejections30.success_iff _ _ _ _ _ _ _ _).mp common).1
  exact ⟨runtime.1,runtime.2.1,runtime.2.2.1,runtime.2.2.2.2⟩
#print axioms transfer_binding

/-- Complete extracted preparation Result is invariant under the overwritten
original root, including both error layers. This is a pure source law, not an
assertion about native timing, memory or observer events. -/
theorem transfer_root_ignored
    (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestPrivateTransferWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (root : Array U32 8#usize) :
    pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1 p w
      {context with runtime_binding := {context.runtime_binding with anchor_root := root}} snapshot =
    pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1 p w context snapshot := rfl
#print axioms transfer_root_ignored

/-- The frozen wrapper validates these original context coordinates after
replacing the lane-root coordinate. No equation for the overwritten root is
assumed or inferred. -/
theorem withdrawal_binding
    (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestWithdrawalWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1 p w context snapshot = ok (.Ok c)) :
    context.runtime_binding.pool=p.pool ∧
    context.runtime_binding.deployment_domain=p.deployment_domain ∧
    context.runtime_binding.anchor_sequence=p.anchor_sequence ∧
    context.runtime_binding.asset_id=p.asset_id := by
  obtain ⟨root,_,_,hc⟩ := PV_RunJoin_OuterPrefix30.withdrawal p w context snapshot c h
  have common := PV_RunJoin_OuterCommonFacts30.common_return _ _ _ _ _ _ _ _ hc
  have runtime := ((PV_RunJoin_RuntimeRejections30.success_iff _ _ _ _ _ _ _ _).mp common).1
  exact ⟨runtime.1,runtime.2.1,runtime.2.2.1,runtime.2.2.2.2⟩
#print axioms withdrawal_binding

/-- Complete extracted preparation Result is invariant under the overwritten
original root, including both error layers. This is a pure source law, not an
assertion about native timing, memory or observer events. -/
theorem withdrawal_root_ignored
    (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestWithdrawalWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (root : Array U32 8#usize) :
    pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1 p w
      {context with runtime_binding := {context.runtime_binding with anchor_root := root}} snapshot =
    pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1 p w context snapshot := rfl
#print axioms withdrawal_root_ignored
end R1Z.PV_RunJoin_PreparationContext32

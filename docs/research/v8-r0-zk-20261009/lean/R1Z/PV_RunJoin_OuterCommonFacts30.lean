import R1Z.PV_RunJoin_OuterPrefix30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OuterCommonFacts30
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30
open PV_RunJoin_OuterABI30
variable [LaneRoot] [R1Z.BuilderForestAdmissionPort.ExternalLinear] [R1Z.BuilderForestAdmissionPort.Records]

theorem common_return
    (pool domain : Array U8 32#usize) (seq : U64) (anchor nullifier : Array U32 8#usize)
    (asset : U32) (input : pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (h : pool_v1.pair_trace.validate_common pool domain seq anchor nullifier asset input context = ok (.Ok ())) :
    AspisBuilderAdmissionSource.pool_v1.pair_trace.validate_common
      pool domain seq anchor nullifier asset (pairToAdmission input) (contextToAdmission context) = ok (.Ok ()) := by
  have hp := (PV_RunJoin_OuterCall30.runtime_success_iff pool domain seq anchor nullifier asset input context).mp ⟨(),h⟩
  obtain ⟨u,hu⟩ := (PV_RunJoin_RuntimeDomain30.success_iff pool domain seq anchor nullifier asset
    (pairToAdmission input) (contextToAdmission context)).mpr hp
  cases u
  exact hu
#print axioms common_return

theorem transfer
    (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestPrivateTransferWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1
      p w context snapshot = ok (.Ok c)) :
    BuilderAdmissionCommon.CommonFacts (pairToAdmission w.input.pair) := by
  obtain ⟨root,_,_,hc⟩ := PV_RunJoin_OuterPrefix30.transfer p w context snapshot c h
  exact BuilderAdmissionCommon.common_facts _ _ _ _ _ _ _ _ (common_return _ _ _ _ _ _ _ _ hc)
#print axioms transfer

theorem withdrawal
    (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestWithdrawalWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1
      p w context snapshot = ok (.Ok c)) :
    BuilderAdmissionCommon.CommonFacts (pairToAdmission w.input.pair) := by
  obtain ⟨root,_,_,hc⟩ := PV_RunJoin_OuterPrefix30.withdrawal p w context snapshot c h
  exact BuilderAdmissionCommon.common_facts _ _ _ _ _ _ _ _ (common_return _ _ _ _ _ _ _ _ hc)
#print axioms withdrawal
end R1Z.PV_RunJoin_OuterCommonFacts30

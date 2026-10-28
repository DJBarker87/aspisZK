import R1Z.PV_RunJoin_OuterCall30
import R1Z.PV_RunJoin_DecoderReturn29
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OuterPrefix30
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30
variable [LaneRoot] [R1Z.BuilderForestAdmissionPort.ExternalLinear] [R1Z.BuilderForestAdmissionPort.Records]

theorem transfer
    (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestPrivateTransferWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1 p w context snapshot = ok (.Ok c)) :
    ∃ anchor, pool_v1.pair_forest_trace.lane_root w.input.pair = ok (.Ok anchor) ∧
      pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1 {p with anchor_root := anchor} = ok (.Ok ()) ∧
      pool_v1.pair_trace.validate_common p.pool p.deployment_domain p.anchor_sequence
        anchor p.nullifier p.asset_id w.input.pair
        {context with runtime_binding := {context.runtime_binding with anchor_root := anchor}} = ok (.Ok ()) := by
  unfold pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1 at h
  pv_peel h with r hr
  pv_peel h with cf hf
  cases cf with
  | Break residual => exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
  | Continue anchor =>
    have he := PV_RunJoin_DecoderReturn29.branch_continue r anchor hf
    subst r
    pv_peel h with checked hp
    pv_peel h with mapped hm
    pv_peel h with flow hf1
    cases flow with
    | Break residual => exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
    | Continue u =>
      cases u
      have he := PV_RunJoin_DecoderReturn29.branch_continue mapped () hf1
      subst mapped
      have he := BuilderAdmissionCommon.mapErr_success _ checked _ hm
      subst checked
      pv_peel h with updated hu
      unfold pool_v1.pair_forest_trace.temporary_context at hu
      cases Result.ok.inj hu
      pv_peel h with checked hc
      pv_peel h with flow hf2
      cases flow with
      | Break residual => exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
      | Continue u =>
        cases u
        have he := PV_RunJoin_DecoderReturn29.branch_continue checked () hf2
        subst checked
        exact ⟨anchor,hr,hp,hc⟩
#print axioms transfer

theorem withdrawal
    (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestWithdrawalWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1 p w context snapshot = ok (.Ok c)) :
    ∃ anchor, pool_v1.pair_forest_trace.lane_root w.input.pair = ok (.Ok anchor) ∧
      pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1 {p with anchor_root := anchor} = ok (.Ok ()) ∧
      pool_v1.pair_trace.validate_common p.pool p.deployment_domain p.anchor_sequence
        anchor p.nullifier p.asset_id w.input.pair
        {context with runtime_binding := {context.runtime_binding with anchor_root := anchor}} = ok (.Ok ()) := by
  unfold pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1 at h
  pv_peel h with r hr
  pv_peel h with cf hf
  cases cf with
  | Break residual => exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
  | Continue anchor =>
    have he := PV_RunJoin_DecoderReturn29.branch_continue r anchor hf
    subst r
    pv_peel h with checked hp
    pv_peel h with mapped hm
    pv_peel h with flow hf1
    cases flow with
    | Break residual => exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
    | Continue u =>
      cases u
      have he := PV_RunJoin_DecoderReturn29.branch_continue mapped () hf1
      subst mapped
      have he := BuilderAdmissionCommon.mapErr_success _ checked _ hm
      subst checked
      pv_peel h with updated hu
      unfold pool_v1.pair_forest_trace.temporary_context at hu
      cases Result.ok.inj hu
      pv_peel h with checked hc
      pv_peel h with flow hf2
      cases flow with
      | Break residual => exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
      | Continue u =>
        cases u
        have he := PV_RunJoin_DecoderReturn29.branch_continue checked () hf2
        subst checked
        exact ⟨anchor,hr,hp,hc⟩
#print axioms withdrawal
end R1Z.PV_RunJoin_OuterPrefix30

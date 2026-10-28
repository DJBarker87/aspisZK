import R1Z.PV_RunJoin_OuterCall30
import R1Z.PV_RunJoin_DecoderReturn29
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OuterReturns30
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30
open PV_RunJoin_OuterABI30
variable [LaneRoot] [R1Z.BuilderForestAdmissionPort.ExternalLinear] [R1Z.BuilderForestAdmissionPort.Records]

theorem transfer_inner
    (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestPrivateTransferWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1
      p w context snapshot = ok (.Ok c)) :
    ∃ anchor, pool_v1.pair_forest_trace.lane_root w.input.pair = ok (.Ok anchor) ∧
      BuilderForestAdmissionPort.pool_v1.pair_forest_trace.compile_forest_from_copies
        (inputToForest w.input) w.recipient.value (some (noteToForest w.recipient))
        (noteToForest w.change)
        (publicToForest ⟨p.anchor_root,p.nullifier,some p.recipient_commitment,p.change_commitment,p.asset_id⟩)
        anchor (snapshotToForest snapshot) = ok (.Ok (compilationToForest c)) := by
  unfold pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1 at h
  pv_peel h with r hr
  pv_peel h with cf hf
  cases cf with
  | Break residual => exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
  | Continue anchor =>
    have he := PV_RunJoin_DecoderReturn29.branch_continue r anchor hf
    subst r
    refine ⟨anchor,hr,?_⟩
    repeat' first
      | exact PV_RunJoin_OuterCall30.inner_return _ _ _ _ _ _ _ _ h
      | (pv_peel h with value hvalue)
      | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
      | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
      | (pv_if h)
      | (have _test : Bool := value; cases value <;> simp only [Bool.false_eq_true,↓reduceIte] at h)
      | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value)
#print axioms transfer_inner

theorem withdrawal_inner
    (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestWithdrawalWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1
      p w context snapshot = ok (.Ok c)) :
    ∃ anchor, pool_v1.pair_forest_trace.lane_root w.input.pair = ok (.Ok anchor) ∧
      BuilderForestAdmissionPort.pool_v1.pair_forest_trace.compile_forest_from_copies
        (inputToForest w.input) p.amount none (noteToForest w.change)
        (publicToForest ⟨p.anchor_root,p.nullifier,none,p.change_commitment,p.asset_id⟩)
        anchor (snapshotToForest snapshot) = ok (.Ok (compilationToForest c)) := by
  unfold pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1 at h
  pv_peel h with r hr
  pv_peel h with cf hf
  cases cf with
  | Break residual => exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
  | Continue anchor =>
    have he := PV_RunJoin_DecoderReturn29.branch_continue r anchor hf
    subst r
    refine ⟨anchor,hr,?_⟩
    repeat' first
      | exact PV_RunJoin_OuterCall30.inner_return _ _ _ _ _ _ _ _ h
      | (pv_peel h with value hvalue)
      | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
      | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
      | (pv_if h)
      | (have _test : Bool := value; cases value <;> simp only [Bool.false_eq_true,↓reduceIte] at h)
      | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value)
#print axioms withdrawal_inner
end R1Z.PV_RunJoin_OuterReturns30

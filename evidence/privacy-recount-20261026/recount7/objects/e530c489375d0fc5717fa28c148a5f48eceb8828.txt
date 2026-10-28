import R1Z.PV_RunJoin_CheckedAddGuard30
import R1Z.PV_RunJoin_OuterBounds30
import R1Z.PV_RunJoin_Conservation29
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OuterConservation30
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30
variable [LaneRoot] [R1Z.BuilderForestAdmissionPort.ExternalLinear] [R1Z.BuilderForestAdmissionPort.Records]

theorem transfer
    (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestPrivateTransferWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1 p w context snapshot = ok (.Ok c)) :
    PV_RunJoin_Conservation29.transferDomain w.input.pair.value w.recipient.value w.change.value := by
  unfold PV_RunJoin_Conservation29.transferDomain
  unfold pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1 at h
  repeat' first
    | (refine ⟨PV_RunJoin_CheckedAddGuard30.positive _ (by assumption),
        PV_RunJoin_CheckedAddGuard30.positive _ (by assumption),
        PV_RunJoin_OuterBounds30.bound_of_guard _ (by assumption),
        PV_RunJoin_OuterBounds30.bound_of_guard _ (by assumption),?_⟩
       apply PV_RunJoin_CheckedAddGuard30.value <;> assumption)
    | (have he : value = 1073741824#u32 := (Result.ok.inj hvalue).symm; subst value)
    | (pv_peel h with value hvalue)
    | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
    | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
    | (pv_if h)
    | (have _test : Bool := value; cases value <;> simp only [Bool.false_eq_true,↓reduceIte] at h)
    | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value <;> pv_head h)
#print axioms transfer

theorem withdrawal
    (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestWithdrawalWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1 p w context snapshot = ok (.Ok c)) :
    PV_RunJoin_Conservation29.withdrawalDomain w.input.pair.value p.amount w.change.value := by
  unfold PV_RunJoin_Conservation29.withdrawalDomain
  unfold pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1 at h
  repeat' first
    | (refine ⟨PV_RunJoin_CheckedAddGuard30.positive _ (by assumption),
        PV_RunJoin_OuterBounds30.bound_of_guard _ (by assumption),?_⟩
       apply PV_RunJoin_CheckedAddGuard30.value <;> assumption)
    | (have he : value = 1073741824#u32 := (Result.ok.inj hvalue).symm; subst value)
    | (pv_peel h with value hvalue)
    | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
    | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
    | (pv_if h)
    | (have _test : Bool := value; cases value <;> simp only [Bool.false_eq_true,↓reduceIte] at h)
    | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value <;> pv_head h)
#print axioms withdrawal
end R1Z.PV_RunJoin_OuterConservation30

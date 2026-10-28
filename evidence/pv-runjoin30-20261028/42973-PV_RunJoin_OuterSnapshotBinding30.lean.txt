import R1Z.PV_RunJoin_OuterFuns30
import R1Z.PV_RunJoin_RuntimePrimitives30
import R1Z.PV_RunJoin_HeadControl29
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OuterSnapshotBinding30
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30

theorem bytes_equal (a b : Array U8 32#usize) {bit : Bool}
    (hc : Aeneas.Std.core.array.equality.PartialEqArray.ne Aeneas.Std.core.cmp.PartialEqU8 a b = ok bit)
    (hp : ¬bit=true) : a=b := by
  have hz : bit=false := Bool.eq_false_iff.mpr hp
  rw [hz,PV_RunJoin_RuntimePrimitives30.bytes_ne] at hc
  simpa only [Result.ok.injEq,decide_eq_false_iff_not,not_not] using hc
#print axioms bytes_equal

variable [LaneRoot] [BuilderForestAdmissionPort.ExternalLinear] [BuilderForestAdmissionPort.Records]

theorem transfer
    (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestPrivateTransferWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1 p w context snapshot = ok (.Ok c)) :
    snapshot.pool=p.pool ∧ snapshot.deployment_domain=p.deployment_domain := by
  unfold pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1 at h
  repeat' first
    | exact ⟨bytes_equal _ _ (by assumption) (by assumption),bytes_equal _ _ (by assumption) (by assumption)⟩
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
    snapshot.pool=p.pool ∧ snapshot.deployment_domain=p.deployment_domain := by
  unfold pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1 at h
  repeat' first
    | exact ⟨bytes_equal _ _ (by assumption) (by assumption),bytes_equal _ _ (by assumption) (by assumption)⟩
    | (pv_peel h with value hvalue)
    | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
    | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
    | (pv_if h)
    | (have _test : Bool := value; cases value <;> simp only [Bool.false_eq_true,↓reduceIte] at h)
    | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value <;> pv_head h)
#print axioms withdrawal
end R1Z.PV_RunJoin_OuterSnapshotBinding30

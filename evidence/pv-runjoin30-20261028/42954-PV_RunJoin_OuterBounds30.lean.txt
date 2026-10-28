import R1Z.PV_RunJoin_OuterPrefix30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OuterBounds30
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30
variable [LaneRoot] [R1Z.BuilderForestAdmissionPort.ExternalLinear] [R1Z.BuilderForestAdmissionPort.Records]

theorem bound_of_guard (n : U32) (h : ¬ n ≥ 1073741824#u32) : n.val<2^30 := by
  have h' : ¬1073741824≤n.val := by simpa only [UScalar.le_equiv,UScalar.ofNatCore_val_eq] using h
  exact Nat.lt_of_not_ge h'
#print axioms bound_of_guard

theorem transfer
    (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestPrivateTransferWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1
      p w context snapshot = ok (.Ok c)) :
    w.recipient.value.val<2^30 ∧ w.change.value.val<2^30 := by
  unfold pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1 at h
  repeat' first
    | exact ⟨bound_of_guard _ (by assumption),bound_of_guard _ (by assumption)⟩
    | (have he : value = 1073741824#u32 := (Result.ok.inj hvalue).symm; subst value)
    | (pv_peel h with value hvalue)
    | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
    | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
    | (pv_if h)
    | (have _test : Bool := value; cases value <;> simp only [Bool.false_eq_true,↓reduceIte] at h)
    | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value <;> pv_head h)
#print axioms transfer

theorem withdrawal_change
    (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestWithdrawalWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1
      p w context snapshot = ok (.Ok c)) : w.change.value.val<2^30 := by
  unfold pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1 at h
  repeat' first
    | exact bound_of_guard _ (by assumption)
    | (have he : value = 1073741824#u32 := (Result.ok.inj hvalue).symm; subst value)
    | (pv_peel h with value hvalue)
    | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
    | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
    | (pv_if h)
    | (have _test : Bool := value; cases value <;> simp only [Bool.false_eq_true,↓reduceIte] at h)
    | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value <;> pv_head h)
#print axioms withdrawal_change

theorem withdrawal_public (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (h : pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1 p = ok (.Ok ())) :
    p.amount.val<2^30 := by
  unfold pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1 at h
  repeat' first
    | exact bound_of_guard _ (by assumption)
    | (have he : value = 1073741824#u32 := (Result.ok.inj hvalue).symm; subst value)
    | (pv_peel h with value hvalue)
    | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
    | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
    | (pv_if h)
    | (have _test : Bool := value; cases value <;> simp only [Bool.false_eq_true,↓reduceIte] at h)
    | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value <;> pv_head h)
#print axioms withdrawal_public

theorem withdrawal_amount
    (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestWithdrawalWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1
      p w context snapshot = ok (.Ok c)) : p.amount.val<2^30 := by
  obtain ⟨root,_,hp,_⟩ := PV_RunJoin_OuterPrefix30.withdrawal p w context snapshot c h
  exact withdrawal_public {p with anchor_root := root} hp
#print axioms withdrawal_amount
end R1Z.PV_RunJoin_OuterBounds30

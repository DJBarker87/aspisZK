import R1Z.PV_RunJoin_SemanticChange30
import R1Z.PV_RunJoin_OuterChecked30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticOptions30
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30 R0Z.WriterRefine R1J.SpendWitnessMap
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
variable [LaneRoot]

theorem withdrawal_nonzero (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (h : pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1 p = ok (.Ok ())) :
    p.amount≠0#u32 := by
  unfold pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1 at h
  repeat' first
    | assumption
    | (pv_peel h with value hvalue)
    | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
    | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
    | (pv_if h)
    | (have _test : Bool := value; cases value <;> simp only [Bool.false_eq_true,↓reduceIte] at h)
    | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value <;> pv_head h)
#print axioms withdrawal_nonzero

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem field_nonzero (n : U32) (hn : n≠0#u32) (bound : n.val<2^30) : (n.val : K)≠0 := by
  intro h
  have hf : (n.val : F)=0 := by
    apply (ι : F →+* K).injective
    simpa only [map_natCast,map_zero] using h
  have hv := congrArg (fun x : F => x.val) hf
  change (n.val : ZMod 2147483647).val=0 at hv
  rw [ZMod.val_natCast,Nat.mod_eq_of_lt (by omega)] at hv
  exact hn (UScalar.eq_of_val_eq hv)
#print axioms field_nonzero

theorem transfer_shape
    (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestPrivateTransferWitnessV1)
    (root : Array U32 8#usize) (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) :
    AspisR1.PublicOptionShape.canonical (PV_RunJoin_SemanticChange30.statement (K := K)
      (PV_RunJoin_OuterChecked30.transferInput p w root snapshot c)) := ⟨rfl,rfl⟩
#print axioms transfer_shape

theorem withdrawal_shape
    (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestWithdrawalWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (root : Array U32 8#usize) (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1 p w context snapshot = ok (.Ok c)) :
    AspisR1.PublicOptionShape.canonical (PV_RunJoin_SemanticChange30.statement (K := K)
      (PV_RunJoin_OuterChecked30.withdrawalInput p w root snapshot c)) := by
  obtain ⟨anchor,_,hp,_⟩ := PV_RunJoin_OuterPrefix30.withdrawal p w context snapshot c h
  have hz := withdrawal_nonzero {p with anchor_root := anchor} hp
  have hb := PV_RunJoin_OuterBounds30.withdrawal_amount p w context snapshot c h
  refine ⟨rfl,rfl,?_⟩
  change (some (ι (liftU (K := F) p.amount))) ≠ some 0
  intro he
  apply field_nonzero (K := K) p.amount hz hb
  simpa only [liftU,map_natCast] using Option.some.inj he
#print axioms withdrawal_shape

theorem withdrawal_variant
    (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestWithdrawalWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (root : Array U32 8#usize) (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1 p w context snapshot = ok (.Ok c)) :
    AspisR1.SpendRelation.variantOutput (PV_RunJoin_SemanticChange30.statement (K := K)
      (PV_RunJoin_OuterChecked30.withdrawalInput p w root snapshot c))
      (PV_RunJoin_SemanticChange30.witness (K := K)
      (PV_RunJoin_OuterChecked30.withdrawalInput p w root snapshot c)) := by
  have hb := PV_RunJoin_OuterBounds30.withdrawal_amount p w context snapshot c h
  change some (ι (liftU (K := F) p.amount)) = some ((p.amount.val % 2^30 : Nat) : K)
  rw [Nat.mod_eq_of_lt hb]
  simp only [liftU,map_natCast]
#print axioms withdrawal_variant
end R1Z.PV_RunJoin_SemanticOptions30

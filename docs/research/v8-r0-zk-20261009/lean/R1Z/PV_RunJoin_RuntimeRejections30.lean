import R1Z.PV_RunJoin_RuntimeGuards30
import R1Z.PV_Src_CompilerTactic
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RuntimeRejections30
open Aeneas Aeneas.Std Result AspisBuilderAdmissionSource
open pool_v1.pair_trace PV_RunJoin_RuntimeGuards30
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem mapped_unit {E V O : Type} (m : Result (core.result.Result Unit E))
    (f : core.ops.function.FnOnce O E V) (c : O) :
    (do let r ← m; BuilderAdmissionStd.mapErr f r c) = ok (.Ok ()) ↔
      m = ok (.Ok ()) := by
  constructor
  · intro h
    pv_peel h with r hr
    have he := BuilderAdmissionCommon.mapErr_success f r c h
    rw [he] at hr
    exact hr
  · intro h
    rw [h]
    rfl
#print axioms mapped_unit

variable (pool domain : Array U8 32#usize) (seq : U64)
    (anchor nullifier : Array U32 8#usize) (asset : U32)
    (input : PoolV1PairInputNoteWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)

theorem success_iff :
    validate_common pool domain seq anchor nullifier asset input context = ok (.Ok ()) ↔
      Runtime pool domain seq anchor asset context ∧
      nullifier ∉ context.spent_nullifiers.val ∧ Digests input ∧ Values input ∧
      input.pair_leaf.require_selected_spendable input.selected_second = ok (.Ok ()) := by
  rw [source_result]
  by_cases hr : Runtime pool domain seq anchor asset context <;>
    by_cases hs : nullifier ∈ context.spent_nullifiers.val <;>
    by_cases hd : Digests input <;> by_cases hv : Values input <;>
    simp only [result,hr,hs,hd,hv,not_true_eq_false,not_false_eq_true,↓reduceIte,
      Result.ok.injEq,reduceCtorEq,mapped_unit,true_and,false_and]
  exact mapped_unit _ _ _
#print axioms success_iff

theorem runtime_error (h : ¬ Runtime pool domain seq anchor asset context) :
    validate_common pool domain seq anchor nullifier asset input context = ok (.Err .RuntimeBinding) := by
  rw [source_result]
  simp only [result,if_pos h]
#print axioms runtime_error

theorem spent_error (hr : Runtime pool domain seq anchor asset context)
    (hs : nullifier ∈ context.spent_nullifiers.val) :
    validate_common pool domain seq anchor nullifier asset input context = ok (.Err .NullifierAlreadySpent) := by
  rw [source_result]
  simp only [result,hr,not_true_eq_false,if_false,if_pos hs]
#print axioms spent_error

theorem digest_error (hr : Runtime pool domain seq anchor asset context)
    (hs : nullifier ∉ context.spent_nullifiers.val) (hd : ¬ Digests input) :
    validate_common pool domain seq anchor nullifier asset input context = ok (.Err .WitnessDigest) := by
  rw [source_result]
  simp only [result,hr,not_true_eq_false,if_false,if_neg hs,if_pos hd]
#print axioms digest_error

theorem value_error (hr : Runtime pool domain seq anchor asset context)
    (hs : nullifier ∉ context.spent_nullifiers.val) (hd : Digests input) (hv : ¬ Values input) :
    validate_common pool domain seq anchor nullifier asset input context = ok (.Err .ValueOutOfRange) := by
  rw [source_result]
  simp only [result,hr,hd,not_true_eq_false,if_false,if_neg hs,if_pos hv]
#print axioms value_error

theorem pair_error (hr : Runtime pool domain seq anchor asset context)
    (hs : nullifier ∉ context.spent_nullifiers.val) (hd : Digests input) (hv : Values input)
    (e : pool_v1.pair_tree_profile.PoolV1PairLeafErrorV1)
    (he : input.pair_leaf.require_selected_spendable input.selected_second = ok (.Err e)) :
    validate_common pool domain seq anchor nullifier asset input context = ok (.Err (.PairLeaf e)) := by
  rw [source_result]
  simp only [result,hr,hd,hv,not_true_eq_false,if_false,if_neg hs,he,bind_tc_ok]
  rfl
#print axioms pair_error
end R1Z.PV_RunJoin_RuntimeRejections30

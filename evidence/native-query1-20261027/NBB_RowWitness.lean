import NBB_RowTrace
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBB_RowWitness
open NBB_RowTrace

theorem steps (step : Fin 4 → Row → Nat) (indices : List (Fin 4)) (before : Row) :
 ∃ after, Steps step indices before after := by
 induction indices generalizing before with
 | nil => exact ⟨before,.nil before⟩
 | cons j js ih =>
  let middle := Function.update before j (step j before)
  obtain ⟨after,tail⟩ := ih middle
  refine ⟨after,.cons ?_ tail⟩
  intro k
  by_cases same : k=j
  · subst k; simp [middle]
  · simp [middle,same]

/-- Every caller-domain input admits linked native-shaped one-store traces,
and their full output is the SAME successful emitted carrier. -/
theorem construct (before : Fin 4 → U64) (power : S7Kani2OwnedRow.K)
 (basis : U32) (terms : Nat)
 (hc : ∀ j, (S7Kani2OwnedRowRefinement.powerLimb power j).val<2^31-1)
 (hb : basis.val<2^31-1) (hp : ∀ j, NBB_Phase.Bound terms (before j).val) :
 ∃ (added : Row) (out : Fin 4 → U64),
 Steps (fun j row => row j+(S7Kani2OwnedRowRefinement.powerLimb power j).val*basis.val)
  [0,1,2,3] (fun j => (before j).val) added ∧
 (if decide (terms%4=3) then Steps (fun j row => AspisV8R17.RawReducer.foldBits (row j))
   [0,1,2,3] added (fun j => (out j).val) else (fun j => (out j).val)=added) ∧
 S7Kani2OwnedRow.residue_owned (S7Kani2OwnedRowRefinement.makeRow before) power basis
  (decide (terms%4=3))=ok (S7Kani2OwnedRowRefinement.makeRow out) := by
 obtain ⟨added,adds⟩ := steps (fun j row => row j+
  (S7Kani2OwnedRowRefinement.powerLimb power j).val*basis.val) [0,1,2,3]
  (fun j => (before j).val)
 obtain ⟨out,run,value,_⟩ := NBB_Row.source before power basis terms hc hb hp
 have model := S7OwnedP6RowContract.source_eq_batched_model
  (fun j => (before j).val) (fun j => (S7Kani2OwnedRowRefinement.powerLimb power j).val)
  basis.val terms
 have fused := S7OwnedP6RowContract.four_lane_fusion
  (fun j => (before j).val) (fun j => (S7Kani2OwnedRowRefinement.powerLimb power j).val)
  basis.val (decide (terms%4=3))
 have outValue : (fun j => (out j).val)=
  S7OwnedP6RowContract.reference (fun j => (before j).val)
   (fun j => (S7Kani2OwnedRowRefinement.powerLimb power j).val) basis.val (decide (terms%4=3)) := by
  funext j
  rw [value]
  exact congrFun (model.symm.trans fused) j
 refine ⟨added,out,adds,?_,run⟩
 cases flag : decide (terms%4=3) with
 | false =>
  simp only [flag,Bool.false_eq_true,if_false]
  have result := source_result _ _ basis.val false added added adds rfl
  exact outValue.trans (by simpa only [flag] using result.symm)
 | true =>
  simp only [flag,if_true]
  obtain ⟨after,folds⟩ := steps (fun j row => AspisV8R17.RawReducer.foldBits (row j)) [0,1,2,3] added
  have result := source_result _ _ basis.val true added after adds folds
  have same : after=(fun j => (out j).val) := result.trans (by simpa only [flag] using outValue.symm)
  simpa only [same] using folds
#print axioms steps
#print axioms construct
end NBB_RowWitness

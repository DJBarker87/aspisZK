import NBB_Row
import S7OwnedP6RowContract
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBB_RowTrace
abbrev Row := Fin 4 → Nat
/-- One native store and its complete pointwise frame. -/
def Frame (j : Fin 4) (value : Nat) (before after : Row) : Prop :=
 ∀ k, after k=if k=j then value else before k
inductive Steps (step : Fin 4 → Row → Nat) : List (Fin 4) → Row → Row → Prop
 | nil (r : Row) : Steps step [] r r
 | cons {j js before middle after}
   (head : Frame j (step j before) before middle)
   (tail : Steps step js middle after) : Steps step (j::js) before after

theorem frame_unique (j : Fin 4) (value : Nat) (before after : Row)
 (frame : Frame j value before after) : after=Function.update before j value := by
 funext k
 rw [frame]
 by_cases same : k=j
 · subst k; simp
 · simp [Function.update_of_ne same,same]

theorem steps_result (step : Fin 4 → Row → Nat) (indices : List (Fin 4)) (before after : Row)
 (trace : Steps step indices before after) :
 after=indices.foldl (fun row j => Function.update row j (step j row)) before := by
 induction trace with
 | nil => rfl
 | cons head tail ih => rw [List.foldl_cons,←frame_unique _ _ _ _ head];exact ih

/-- Linked native add/store and fold/store steps give the entire source row,
without a supplied final row equation. -/
theorem source_result (before limbs : Row) (basis : Nat) (flush : Bool)
 (added after : Row)
 (adds : Steps (fun j row => row j+limbs j*basis) [0,1,2,3] before added)
 (folds : if flush then Steps (fun j row => AspisV8R17.RawReducer.foldBits (row j))
   [0,1,2,3] added after else after=added) :
 after=S7OwnedP6RowContract.reference before limbs basis flush := by
 have ha := steps_result _ _ _ _ adds
 cases flush with
 | false =>
   change after=added at folds
   rw [folds,ha]
   exact S7OwnedP6RowContract.four_lane_fusion before limbs basis false
 | true =>
   change Steps _ _ added after at folds
   rw [steps_result _ _ _ _ folds,ha]
   exact S7OwnedP6RowContract.four_lane_fusion before limbs basis true

/-- The full native four-word output is exactly the emitted cohort result.
Only one-store traces enter; native frame gates and scalar laws construct them. -/
theorem native_result (before out : Fin 4 → U64) (power : S7Kani2OwnedRow.K)
 (basis : U32) (terms : Nat) (added : Row)
 (hc : ∀ j, (S7Kani2OwnedRowRefinement.powerLimb power j).val<2^31-1)
 (hb : basis.val<2^31-1) (hp : ∀ j, NBB_Phase.Bound terms (before j).val)
 (adds : Steps (fun j row => row j+
   (S7Kani2OwnedRowRefinement.powerLimb power j).val*basis.val)
   [0,1,2,3] (fun j => (before j).val) added)
 (folds : if decide (terms%4=3) then
   Steps (fun j row => AspisV8R17.RawReducer.foldBits (row j))
     [0,1,2,3] added (fun j => (out j).val)
   else (fun j => (out j).val)=added) :
 S7Kani2OwnedRow.residue_owned (S7Kani2OwnedRowRefinement.makeRow before) power basis
  (decide (terms%4=3))=ok (S7Kani2OwnedRowRefinement.makeRow out) := by
 have values := source_result (fun j => (before j).val)
  (fun j => (S7Kani2OwnedRowRefinement.powerLimb power j).val)
  basis.val (decide (terms%4=3)) added (fun j => (out j).val) adds folds
 have model := S7OwnedP6RowContract.source_eq_batched_model
  (fun j => (before j).val) (fun j => (S7Kani2OwnedRowRefinement.powerLimb power j).val) basis.val terms
 have fused := S7OwnedP6RowContract.four_lane_fusion
  (fun j => (before j).val) (fun j => (S7Kani2OwnedRowRefinement.powerLimb power j).val)
  basis.val (decide (terms%4=3))
 obtain ⟨y,run,hy,_⟩ := NBB_Row.source before power basis terms hc hb hp
 have same : out=y := by
  funext j
  apply UScalar.eq_of_val_eq
  have v := congrFun (values.trans (fused.symm.trans model)) j
  exact v.trans (hy j).symm
 simpa only [same] using run
#print axioms frame_unique
#print axioms steps_result
#print axioms source_result
#print axioms native_result
end NBB_RowTrace

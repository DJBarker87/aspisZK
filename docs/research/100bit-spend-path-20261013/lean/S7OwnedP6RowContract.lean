import S7OwnedP6ScalarProof
import Mathlib.Tactic.FinCases

/-! Finite four-lane loop contract for the literal frozen source fragments.
The Kani frame checks certify each source fragment separately. This file
proves the ordering/fusion fact; it does not certify the enclosing Vec loop. -/
set_option autoImplicit false
namespace S7OwnedP6RowContract
open AspisV8R17.RawReducer
abbrev Row := Fin 4 → Nat

def visit (step : Fin 4 → Row → Row) (row : Row) : Row :=
  step 3 (step 2 (step 1 (step 0 row)))

def source (row limbs : Row) (basis : Nat) (flush : Bool) : Row :=
  let added := visit (fun j r => Function.update r j (r j + limbs j*basis)) row
  if flush then visit (fun j r => Function.update r j (foldBits (r j))) added
  else added

def reference (row limbs : Row) (basis : Nat) (flush : Bool) : Row :=
  fun j => if flush then foldBits (row j+limbs j*basis) else row j+limbs j*basis

/-- The literal add pass followed by the optional fold pass equals the owned
per-lane fused transition. No commutativity of mutable effects is assumed. -/
theorem four_lane_fusion (row limbs : Row) (basis : Nat) (flush : Bool) :
    source row limbs basis flush = reference row limbs basis flush := by
  funext j
  fin_cases j <;> cases flush <;>
    simp [source,reference,visit,Function.update]

/-- Instantiate the fusion with the actual transaction cadence; the result
is exactly the existing Lean model's four independent sourcePush calls. -/
theorem source_eq_batched_model (row limbs : Row) (basis terms : Nat) :
    source row limbs basis (decide (terms%4=3)) =
      fun j => AspisR1BatchedFoldSourceStep.sourcePush terms (row j) (limbs j*basis) := by
  rw [four_lane_fusion]
  funext j
  simp only [reference,AspisR1BatchedFoldSourceStep.sourcePush,
    foldBits_eq_fold31,fold31,AspisR1BatchedFoldSourceStep.fold,
    AspisR1BatchedFoldSourceStep.limbBase,decide_eq_true_eq]

#print axioms four_lane_fusion
#print axioms source_eq_batched_model
end S7OwnedP6RowContract

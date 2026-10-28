-- Inherited body, import-only deployed-cohort retarget.
import NCD_B_NBQ_Filled
set_option autoImplicit false
noncomputable section
namespace NBS_FilledTrace
/-- Initialization trace of a returned private allocation. The backing
allocation is fixed, and each append initializes exactly the next cell.
This is a value trace, not a native reserve/resize ownership law. -/
inductive Initializes {T : Type} (value : T) : Nat → List T → Prop
  | zero : Initializes value 0 []
  | step {n xs} : Initializes value n xs → Initializes value (n+1) (xs++[value])

theorem contents {T : Type} {value : T} {n : Nat} {xs : List T}
    (trace : Initializes value n xs) : xs=List.replicate n value := by
  induction trace with
  | zero => rfl
  | @step n xs trace ih =>
    rw [ih,List.replicate_succ']

theorem initialized {T : Type} {value : T} {n : Nat} {xs : List T}
    (trace : Initializes value n xs) : xs.length=n ∧ ∀ i, i<n → xs[i]?=some value := by
  rw [contents trace]
  exact ⟨List.length_replicate,fun i hi => NBQ_Filled.selected n value i hi⟩

#print axioms contents
#print axioms initialized
end NBS_FilledTrace

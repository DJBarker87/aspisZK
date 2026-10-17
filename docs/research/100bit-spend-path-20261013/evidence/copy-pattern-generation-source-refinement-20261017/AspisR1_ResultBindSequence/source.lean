import Aeneas.Std

/-! Generic Result sequencing before generated scalar/array instantiation. -/
set_option autoImplicit false
namespace AspisR1.ResultBindSequence
open Aeneas.Std Result

theorem group_first {A B C : Type} (read : Result A)
    (step : A → Result B) (next : B → Result C) :
    (do let a ← read; let b ← step a; next b) =
      (do let b ← (do let a ← read; step a); next b) := by
  cases read <;> rfl

#print axioms group_first
end AspisR1.ResultBindSequence

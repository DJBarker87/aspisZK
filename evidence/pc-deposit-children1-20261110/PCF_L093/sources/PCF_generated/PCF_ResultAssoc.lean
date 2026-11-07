import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCF_ResultAssoc
theorem assoc {A B C : Type} (x : Result A) (f : A → Result B) (g : B → Result C) :
    (do let a ← x; let b ← f a; g b) =
    (do let b ← (do let a ← x; f a); g b) := by cases x <;> rfl
#print axioms assoc
end PCF_ResultAssoc

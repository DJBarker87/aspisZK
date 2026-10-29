import Aeneas
set_option autoImplicit false
namespace NDH_ResultLaws
open Aeneas Aeneas.Std Result

theorem right {A : Type} (m : Result A) : (do let x ← m; ok x) = m := by
  cases m <;> rfl

theorem assoc {A B C : Type} (m : Result A) (f : A → Result B)
    (g : B → Result C) :
    (do let x ← (do let a ← m; f a); g x) =
      (do let a ← m; let x ← f a; g x) := by
  cases m <;> rfl

#print axioms right
#print axioms assoc
end NDH_ResultLaws

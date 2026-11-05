import NHT_BindOn
set_option autoImplicit false
namespace NHT_BindAssoc
open Aeneas Aeneas.Std Result
/-- Explicit small monadic association, preserving failure and divergence. -/
theorem source {A B C : Type} (m : Result A) (f : A → Result B) (g : B → Result C) :
 (do let b ← (do let a ← m; f a); g b)=
 (do let a ← m; let b ← f a; g b) := by
 cases m <;> rfl
#print axioms source
end NHT_BindAssoc

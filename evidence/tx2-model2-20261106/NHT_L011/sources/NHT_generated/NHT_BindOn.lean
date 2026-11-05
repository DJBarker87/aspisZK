import VTop_Model
set_option autoImplicit false
namespace NHT_BindOn
open Aeneas Aeneas.Std Result
theorem reached {A B : Type} (m : Result A) (f g : A → Result B)
 (child : ∀ a, m=ok a → f a=g a) :
 (do let a ← m;f a)=(do let a ← m;g a) := by
 cases m with
 | ok a => exact child a rfl
 | fail e => rfl
 | div => rfl
#print axioms reached
end NHT_BindOn

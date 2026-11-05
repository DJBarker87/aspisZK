import NFW_Bind
set_option autoImplicit false
namespace AspisR1.NHL_BindOn
open Aeneas Aeneas.Std Result
/-- A callee equality is needed only for an actual successful predecessor.
Failure/divergence cannot manufacture a continuation obligation. -/
theorem reached {A B : Type} (m : Result A) (f g : A → Result B)
 (child : ∀ a, m=ok a → f a=g a) :
 (do let a ← m; f a)=(do let a ← m; g a) := by
 cases m with
 | ok a => exact child a rfl
 | fail e => rfl
 | div => rfl
#print axioms reached
end AspisR1.NHL_BindOn

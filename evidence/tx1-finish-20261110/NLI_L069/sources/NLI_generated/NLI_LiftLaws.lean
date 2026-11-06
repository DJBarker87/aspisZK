import NLI_MonadNotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_LiftLaws
open Aeneas Aeneas.Std AspisR1PublicPreparation
open PreparedHashCode (Code run)
/-- Preserve the equation of a pure Result call when comparing continuations.
The equation is derived by case analysis, never an external child endpoint. -/
theorem congr_lift {A B : Type} (r : Result A) (k l : A → Code B)
 (tails : ∀ a, r = .ok a → run (k a) = run (l a)) :
 run ((liftM r : Code A) >>= k) = run ((liftM r : Code A) >>= l) := by
 cases r with
 | ok a => exact tails a rfl
 | fail e => rfl
 | div => rfl
#print axioms congr_lift
end AspisR1.NLI_LiftLaws
end

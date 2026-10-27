import RPv_FJk_PolynomialMap
import RPv_ExtractedMaskTerminalHorner
set_option autoImplicit false
namespace AspisR1.FJk_PolynomialHorner
variable {K : Type} [Field K]
/-- Join the symbolic forward polynomial with the maintained source Horner model. -/
theorem value (theta : K) (xs : List K) :
    FJk_PolynomialMap.polynomial theta xs=TerminalHornerCore.sourceMixHorner theta xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change x+theta*FJk_PolynomialMap.polynomial theta xs=_
    rw [ih,TerminalHornerCore.sourceMixHorner_cons]
    ring
#print axioms value
end AspisR1.FJk_PolynomialHorner

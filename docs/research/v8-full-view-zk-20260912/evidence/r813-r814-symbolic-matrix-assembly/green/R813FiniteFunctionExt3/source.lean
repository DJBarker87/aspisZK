import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Card
set_option autoImplicit false
namespace AspisV8R19.R813FiniteFunctionExt3
variable {R : Type*}
theorem fin3_ext (a b : Fin 3 → R)
    (h0 : a 0 = b 0)
    (h1 : a 1 = b 1)
    (h2 : a 2 = b 2)
    : a = b := by
  funext i
  fin_cases i <;> assumption
#print axioms fin3_ext
end AspisV8R19.R813FiniteFunctionExt3

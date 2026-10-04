import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Card
set_option autoImplicit false
namespace AspisV8R19.R813FiniteFunctionExt4
variable {R : Type*}
theorem fin4_ext (a b : Fin 4 → R)
    (h0 : a 0 = b 0)
    (h1 : a 1 = b 1)
    (h2 : a 2 = b 2)
    (h3 : a 3 = b 3)
    : a = b := by
  funext i
  fin_cases i <;> assumption
#print axioms fin4_ext
end AspisV8R19.R813FiniteFunctionExt4

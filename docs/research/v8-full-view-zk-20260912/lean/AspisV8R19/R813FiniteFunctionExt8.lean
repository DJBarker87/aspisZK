import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Card
set_option autoImplicit false
namespace AspisV8R19.R813FiniteFunctionExt8
variable {R : Type*}
theorem fin8_ext (a b : Fin 8 → R)
    (h0 : a 0 = b 0)
    (h1 : a 1 = b 1)
    (h2 : a 2 = b 2)
    (h3 : a 3 = b 3)
    (h4 : a 4 = b 4)
    (h5 : a 5 = b 5)
    (h6 : a 6 = b 6)
    (h7 : a 7 = b 7)
    : a = b := by
  funext i
  fin_cases i <;> assumption
#print axioms fin8_ext
end AspisV8R19.R813FiniteFunctionExt8

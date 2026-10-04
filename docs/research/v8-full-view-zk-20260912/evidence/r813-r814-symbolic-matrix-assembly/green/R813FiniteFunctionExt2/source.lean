import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Card
set_option autoImplicit false
namespace AspisV8R19.R813FiniteFunctionExt2
variable {R : Type*}
theorem fin2_ext (a b : Fin 2 → R)
    (h0 : a 0 = b 0)
    (h1 : a 1 = b 1)
    : a = b := by
  funext i
  fin_cases i <;> assumption
#print axioms fin2_ext
end AspisV8R19.R813FiniteFunctionExt2

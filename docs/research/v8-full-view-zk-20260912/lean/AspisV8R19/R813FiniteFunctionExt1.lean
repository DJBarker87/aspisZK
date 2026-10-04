import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Card
set_option autoImplicit false
namespace AspisV8R19.R813FiniteFunctionExt1
variable {R : Type*}
theorem fin1_ext (a b : Fin 1 → R)
    (h0 : a 0 = b 0)
    : a = b := by
  funext i
  fin_cases i <;> assumption
#print axioms fin1_ext
end AspisV8R19.R813FiniteFunctionExt1

import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Card
set_option autoImplicit false
namespace AspisV8R19.R813FiniteFunctionExt16
variable {R : Type*}
theorem fin16_ext (a b : Fin 16 → R)
    (h0 : a 0 = b 0)
    (h1 : a 1 = b 1)
    (h2 : a 2 = b 2)
    (h3 : a 3 = b 3)
    (h4 : a 4 = b 4)
    (h5 : a 5 = b 5)
    (h6 : a 6 = b 6)
    (h7 : a 7 = b 7)
    (h8 : a 8 = b 8)
    (h9 : a 9 = b 9)
    (h10 : a 10 = b 10)
    (h11 : a 11 = b 11)
    (h12 : a 12 = b 12)
    (h13 : a 13 = b 13)
    (h14 : a 14 = b 14)
    (h15 : a 15 = b 15)
    : a = b := by
  funext i
  fin_cases i <;> assumption
#print axioms fin16_ext
end AspisV8R19.R813FiniteFunctionExt16

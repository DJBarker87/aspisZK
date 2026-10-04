import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Card
set_option autoImplicit false
namespace AspisV8R19.R813FiniteFunctionExt39
variable {R : Type*}
theorem fin39_ext (a b : Fin 39 → R)
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
    (h16 : a 16 = b 16)
    (h17 : a 17 = b 17)
    (h18 : a 18 = b 18)
    (h19 : a 19 = b 19)
    (h20 : a 20 = b 20)
    (h21 : a 21 = b 21)
    (h22 : a 22 = b 22)
    (h23 : a 23 = b 23)
    (h24 : a 24 = b 24)
    (h25 : a 25 = b 25)
    (h26 : a 26 = b 26)
    (h27 : a 27 = b 27)
    (h28 : a 28 = b 28)
    (h29 : a 29 = b 29)
    (h30 : a 30 = b 30)
    (h31 : a 31 = b 31)
    (h32 : a 32 = b 32)
    (h33 : a 33 = b 33)
    (h34 : a 34 = b 34)
    (h35 : a 35 = b 35)
    (h36 : a 36 = b 36)
    (h37 : a 37 = b 37)
    (h38 : a 38 = b 38)
    : a = b := by
  funext i
  fin_cases i <;> assumption
#print axioms fin39_ext
end AspisV8R19.R813FiniteFunctionExt39

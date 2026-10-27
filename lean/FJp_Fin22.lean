import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
set_option autoImplicit false
namespace AspisR1.FJp_Fin22
/-- Propositional finite induction, insulated from field expressions. -/
theorem all (P : Fin 22 → Prop)
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5)
    (h6 : P 6) (h7 : P 7) (h8 : P 8) (h9 : P 9) (h10 : P 10) (h11 : P 11)
    (h12 : P 12) (h13 : P 13) (h14 : P 14) (h15 : P 15) (h16 : P 16) (h17 : P 17)
    (h18 : P 18) (h19 : P 19) (h20 : P 20) (h21 : P 21) : ∀ j,P j := by
  intro j
  induction j using Fin.induction with
  | zero => exact h0
  | succ k ih =>
    fin_cases k
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
    · exact h8
    · exact h9
    · exact h10
    · exact h11
    · exact h12
    · exact h13
    · exact h14
    · exact h15
    · exact h16
    · exact h17
    · exact h18
    · exact h19
    · exact h20
    · exact h21
#print axioms all
end AspisR1.FJp_Fin22

import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Card

set_option autoImplicit false
namespace AspisV8R19.R815Fin41ExcludeTwo

theorem fin41_except_two {P : Fin 41 → Prop}
    (h1 : P (1 : Fin 41))
    (h2 : P (2 : Fin 41))
    (h3 : P (3 : Fin 41))
    (h4 : P (4 : Fin 41))
    (h5 : P (5 : Fin 41))
    (h7 : P (7 : Fin 41))
    (h8 : P (8 : Fin 41))
    (h9 : P (9 : Fin 41))
    (h10 : P (10 : Fin 41))
    (h11 : P (11 : Fin 41))
    (h12 : P (12 : Fin 41))
    (h13 : P (13 : Fin 41))
    (h14 : P (14 : Fin 41))
    (h15 : P (15 : Fin 41))
    (h16 : P (16 : Fin 41))
    (h17 : P (17 : Fin 41))
    (h18 : P (18 : Fin 41))
    (h19 : P (19 : Fin 41))
    (h20 : P (20 : Fin 41))
    (h21 : P (21 : Fin 41))
    (h22 : P (22 : Fin 41))
    (h23 : P (23 : Fin 41))
    (h24 : P (24 : Fin 41))
    (h25 : P (25 : Fin 41))
    (h26 : P (26 : Fin 41))
    (h27 : P (27 : Fin 41))
    (h28 : P (28 : Fin 41))
    (h29 : P (29 : Fin 41))
    (h30 : P (30 : Fin 41))
    (h31 : P (31 : Fin 41))
    (h32 : P (32 : Fin 41))
    (h33 : P (33 : Fin 41))
    (h34 : P (34 : Fin 41))
    (h35 : P (35 : Fin 41))
    (h36 : P (36 : Fin 41))
    (h37 : P (37 : Fin 41))
    (h38 : P (38 : Fin 41))
    (h39 : P (39 : Fin 41))
    (h40 : P (40 : Fin 41))
: ∀ k : Fin 41, k ≠ (0 : Fin 41) → k ≠ (6 : Fin 41) → P k := by
  intro k h0 h6
  fin_cases k
  · exact False.elim (h0 rfl)
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact False.elim (h6 rfl)
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
  · exact h22
  · exact h23
  · exact h24
  · exact h25
  · exact h26
  · exact h27
  · exact h28
  · exact h29
  · exact h30
  · exact h31
  · exact h32
  · exact h33
  · exact h34
  · exact h35
  · exact h36
  · exact h37
  · exact h38
  · exact h39
  · exact h40
#print axioms fin41_except_two
end AspisV8R19.R815Fin41ExcludeTwo

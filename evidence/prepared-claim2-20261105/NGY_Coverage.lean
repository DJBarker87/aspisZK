import NGY_Association
set_option autoImplicit false
namespace AspisR1.NGY_Coverage

theorem point_cases (point : Nat) (h : point<6) :
 point=0 ∨ point=1 ∨ point=2 ∨ point=3 ∨ point=4 ∨ point=5 := by omega

/-- Join point-specialized certificates without constraining native state,
reply, lane, matrix cells or untouched frame values. -/
theorem six {A : Type} (P : Nat → A → Prop)
 (p0 : ∀ a, P 0 a) (p1 : ∀ a, P 1 a) (p2 : ∀ a, P 2 a)
 (p3 : ∀ a, P 3 a) (p4 : ∀ a, P 4 a) (p5 : ∀ a, P 5 a)
 (point : Nat) (h : point<6) (a : A) : P point a := by
 rcases point_cases point h with rfl|rfl|rfl|rfl|rfl|rfl
 · exact p0 a
 · exact p1 a
 · exact p2 a
 · exact p3 a
 · exact p4 a
 · exact p5 a

theorem lane_cases (lane : Nat) (h : lane<29) :
 lane<15 ∨ (15≤lane ∧ lane<29) := by omega

theorem tiles (lane : Nat) (h : lane<29) :
 lane/4<8 ∧ lane%4<4 ∧ 4*(lane/4)+lane%4=lane := by omega

#print axioms tiles
#print axioms lane_cases
#print axioms point_cases
#print axioms six
end AspisR1.NGY_Coverage

import Mathlib.Tactic
set_option autoImplicit false
namespace NCJ_TensorDomains
/-- Every actual two-fold tensor stage has width 1,4,16 before expansion. -/
def Stage (n : Nat) : Prop := n = 1 ∨ n = 4 ∨ n = 16

theorem positive (n : Nat) (h : Stage n) : 0 < n := by
  rcases h with rfl | rfl | rfl <;> omega

theorem write_bounds (n j lane : Nat) (hn : Stage n) (hj : j < n)
    (hl : lane < 4) : j + lane * n < 4*n ∧ 4*n ≤ 64 := by
  rcases hn with rfl | rfl | rfl <;> omega

/-- Descending j leaves all still unread old entries below the write window. -/
theorem unread_frame (n j old lane : Nat) (hn : Stage n) (hj : j < n)
    (ho : old < j) (hl : lane < 4) : old ≠ j + lane*n := by
  rcases hn with rfl | rfl | rfl <;> omega

theorem lanes_disjoint (n j a b : Nat) (hn : Stage n) (hj : j < n)
    (ha : a < 4) (hb : b < 4) (different : a ≠ b) : j+a*n ≠ j+b*n := by
  rcases hn with rfl | rfl | rfl <;> omega

theorem writes_disjoint (n i j a b : Nat) (hn : Stage n)
    (hi : i < n) (hj : j < n) (ha : a < 4) (hb : b < 4)
    (different : i ≠ j) : i+a*n ≠ j+b*n := by
  rcases hn with rfl | rfl | rfl <;> omega

theorem final_width : 4*(4*(4*1)) = 64 := by decide

theorem dot_caps : 64 < 4096 ∧ 16 < 4096 ∧ 4 < 4096 := by decide

#print axioms positive
#print axioms write_bounds
#print axioms unread_frame
#print axioms lanes_disjoint
#print axioms writes_disjoint
#print axioms final_width
#print axioms dot_caps
end NCJ_TensorDomains

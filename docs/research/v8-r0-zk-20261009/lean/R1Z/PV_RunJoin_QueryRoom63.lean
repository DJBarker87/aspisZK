import Aeneas
set_option autoImplicit false
namespace R1Z.PV_RunJoin_QueryRoom63
/-- Generic scalar resource arithmetic: no large numeral normalization. -/
theorem split (size cap n step fixed : Nat) (fixed_le : fixed≤step)
    (room : size+step*(n+1)≤cap) :
    size+fixed≤cap ∧ ∀ next, next=size+step → next+step*n≤cap := by
  have one : 1≤n+1 := Nat.succ_le_succ (Nat.zero_le n)
  have step_le : step≤step*(n+1) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left step one
  constructor
  · exact (Nat.add_le_add_left (fixed_le.trans step_le) size).trans room
  · intro next value
    have eq : next+step*n=size+step*(n+1) := by
      rw [value,Nat.mul_succ]
      ac_rfl
    rw [eq]
    exact room

theorem widths : 608≤832 := Nat.mul_le_mul_left 16 (by decide : 38≤52)

#print axioms split
#print axioms widths
end R1Z.PV_RunJoin_QueryRoom63

import Aeneas
set_option autoImplicit false
namespace R1Z.PV_RunJoin_QueryRoom63
/-- Scalar resource arithmetic, isolated from generated dictionaries. -/
theorem split (size cap n : Nat) (room : size+832*(n+1)≤cap) :
    size+608≤cap ∧ ∀ next, next=size+832 → next+832*n≤cap := by
  constructor
  · omega
  · intro next value
    omega

#print axioms split
end R1Z.PV_RunJoin_QueryRoom63

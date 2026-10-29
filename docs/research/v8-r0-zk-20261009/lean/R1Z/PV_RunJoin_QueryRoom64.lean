import R1Z.PV_RunJoin_QueryRoom63
set_option autoImplicit false
namespace R1Z.PV_RunJoin_QueryRoom64

theorem length_step (size middle final n step : Nat)
    (first : middle=size+step) (rest : final=middle+step*n) :
    final=size+step*(n+1) := by
  rw [rest,first,Nat.mul_succ]
  ac_rfl

#print axioms length_step
end R1Z.PV_RunJoin_QueryRoom64

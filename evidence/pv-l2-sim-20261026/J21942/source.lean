import R1Z.PV_L2_F6IdentityStep
set_option autoImplicit false
namespace R1Z.PV_L2_F6Identity
open Aeneas Aeneas.Std Result R1CertCheck R1Z.PV_L2_Record
open R1Z.PV_L2_F6IdentityStep
def recorded 
  (c : Slice Std.U32) (co : Std.Usize) (w : Std.Usize) : Recorded Bool :=
  PV_L2_F6FlagLoop.loop 20 (PV_L2_F6IdentityStep.recorded c co w) w w.val true 0#usize
theorem erases 
  (c : Slice Std.U32) (co : Std.Usize) (w : Std.Usize) :
    (recorded c co w).value = id_ok c co w := by
  unfold recorded
  apply PV_L2_F6FlagLoop.erases 20 (PV_L2_F6IdentityStep.recorded c co w) w (id_ok_loop c co w)
  · intro flag index
    rw [recorded_erases]
    exact unroll c co w flag index
  · intro flag index after hs
    rw [recorded_erases] at hs
    exact increment c co w flag index after hs
  · omega
#print axioms erases
end R1Z.PV_L2_F6Identity

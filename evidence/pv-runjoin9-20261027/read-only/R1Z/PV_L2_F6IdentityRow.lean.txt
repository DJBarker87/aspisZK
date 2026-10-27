import R1Z.PV_L2_F6IdentityRowStep
set_option autoImplicit false
namespace R1Z.PV_L2_F6IdentityRow
open Aeneas Aeneas.Std Result R1CertCheck R1Z.PV_L2_Record
open R1Z.PV_L2_F6IdentityRowStep

def recorded 
  (c : Slice Std.U32) (co : Std.Usize) (i : Std.Usize) (w : Std.Usize) : Recorded Bool :=
  PV_L2_F6FlagLoop.loop 10 (PV_L2_F6IdentityRowStep.recorded c co i w) w w.val true 0#usize

theorem erases 
  (c : Slice Std.U32) (co : Std.Usize) (i : Std.Usize) (w : Std.Usize) :
    (recorded c co i w).value = id_row_ok c co i w := by
  unfold recorded
  apply PV_L2_F6FlagLoop.erases 10 (PV_L2_F6IdentityRowStep.recorded c co i w) w
    (id_row_ok_loop c co i w)
  · intro flag index
    rw [PV_L2_F6IdentityRowStep.recorded_erases]
    exact unroll c co i w flag index
  · intro flag index after hs
    rw [PV_L2_F6IdentityRowStep.recorded_erases] at hs
    exact increment c co i w flag index after hs
  · omega

#print axioms erases
end R1Z.PV_L2_F6IdentityRow

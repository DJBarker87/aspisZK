import R1Z.PV_L2_F6PermutationRightStep
set_option autoImplicit false
namespace R1Z.PV_L2_F6PermutationRight
open Aeneas Aeneas.Std Result R1CertCheck R1Z.PV_L2_Record
open R1Z.PV_L2_F6PermutationRightStep

def recorded 
  (lst : Slice Std.U32) (tag : Slice Std.U32) (n : Std.Usize) : Recorded Bool :=
  PV_L2_F6FlagLoop.loop 13 (PV_L2_F6PermutationRightStep.recorded lst tag n) n n.val true 0#usize

theorem erases 
  (lst : Slice Std.U32) (tag : Slice Std.U32) (n : Std.Usize) :
    (recorded lst tag n).value = perm_right_ok lst tag n := by
  unfold recorded
  apply PV_L2_F6FlagLoop.erases 13 (PV_L2_F6PermutationRightStep.recorded lst tag n) n
    (perm_right_ok_loop lst tag n)
  · intro flag index
    rw [PV_L2_F6PermutationRightStep.recorded_erases]
    exact unroll lst tag n flag index
  · intro flag index after hs
    rw [PV_L2_F6PermutationRightStep.recorded_erases] at hs
    exact increment lst tag n flag index after hs
  · omega

#print axioms erases
end R1Z.PV_L2_F6PermutationRight

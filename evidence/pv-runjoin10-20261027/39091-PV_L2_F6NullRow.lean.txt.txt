import R1Z.PV_L2_F6NullRowStep
set_option autoImplicit false
namespace R1Z.PV_L2_F6NullRow
open Aeneas Aeneas.Std Result R1CertCheck R1Z.PV_L2_Record
open R1Z.PV_L2_F6NullRowStep

def recorded 
  (nm : Slice Std.U32) (e : Slice Std.U32) (n : Std.Usize)
  (tag : Slice Std.U32) (r : Std.Usize) (f : Std.Usize) (ff : Std.Usize) : Recorded Bool :=
  PV_L2_F6FlagLoop.loop 14 (PV_L2_F6NullRowStep.recorded nm e n tag r f ff) n n.val true 0#usize

theorem erases 
  (nm : Slice Std.U32) (e : Slice Std.U32) (n : Std.Usize)
  (tag : Slice Std.U32) (r : Std.Usize) (f : Std.Usize) (ff : Std.Usize) :
    (recorded nm e n tag r f ff).value = nvec_row_ok nm e n tag r f ff := by
  unfold recorded
  apply PV_L2_F6FlagLoop.erases 14 (PV_L2_F6NullRowStep.recorded nm e n tag r f ff) n
    (nvec_row_ok_loop nm e n tag r f ff)
  · intro flag index
    rw [PV_L2_F6NullRowStep.recorded_erases]
    exact unroll nm e n tag r f ff flag index
  · intro flag index after hs
    rw [PV_L2_F6NullRowStep.recorded_erases] at hs
    exact increment nm e n tag r f ff flag index after hs
  · omega

#print axioms erases
end R1Z.PV_L2_F6NullRow

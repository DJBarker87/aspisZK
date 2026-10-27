import R1Z.PV_L2_F6LiftsStep
set_option autoImplicit false
namespace R1Z.PV_L2_F6Lifts
open Aeneas Aeneas.Std Result R1CertCheck R1Z.PV_L2_Record
open R1Z.PV_L2_F6LiftsStep
def recorded 
  (o : Slice Std.U32) (u : Slice Std.U32) (id : Slice Std.U32)
  (lw : Slice Std.U32) (loff : Slice Std.U32) (nl : Std.Usize) : Recorded Bool :=
  PV_L2_F6FlagLoop.loop 23 (PV_L2_F6LiftsStep.recorded o u id lw loff nl) nl nl.val true 0#usize
theorem erases 
  (o : Slice Std.U32) (u : Slice Std.U32) (id : Slice Std.U32)
  (lw : Slice Std.U32) (loff : Slice Std.U32) (nl : Std.Usize) :
    (recorded o u id lw loff nl).value = lifts_ok o u id lw loff nl := by
  unfold recorded
  apply PV_L2_F6FlagLoop.erases 23 (PV_L2_F6LiftsStep.recorded o u id lw loff nl) nl (lifts_ok_loop o u id lw loff nl)
  · intro flag index
    rw [recorded_erases]
    exact unroll o u id lw loff nl flag index
  · intro flag index after hs
    rw [recorded_erases] at hs
    exact increment o u id lw loff nl flag index after hs
  · omega
#print axioms erases
end R1Z.PV_L2_F6Lifts

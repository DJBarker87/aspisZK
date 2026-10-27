import R1Z.PV_L2_F6NullStep
set_option autoImplicit false
namespace R1Z.PV_L2_F6Null
open Aeneas Aeneas.Std Result R1CertCheck R1Z.PV_L2_Record
open R1Z.PV_L2_F6NullStep
def recorded 
  (nm : Slice Std.U32) (e : Slice Std.U32) (n : Std.Usize)
  (lst : Slice Std.U32) (tag : Slice Std.U32) (r : Std.Usize) (k : Std.Usize) : Recorded Bool :=
  PV_L2_F6FlagLoop.loop 22 (PV_L2_F6NullStep.recorded nm e n lst tag r k) k k.val true 0#usize
theorem erases 
  (nm : Slice Std.U32) (e : Slice Std.U32) (n : Std.Usize)
  (lst : Slice Std.U32) (tag : Slice Std.U32) (r : Std.Usize) (k : Std.Usize) :
    (recorded nm e n lst tag r k).value = nvec_ok nm e n lst tag r k := by
  unfold recorded
  apply PV_L2_F6FlagLoop.erases 22 (PV_L2_F6NullStep.recorded nm e n lst tag r k) k (nvec_ok_loop nm e n lst tag r k)
  · intro flag index
    rw [recorded_erases]
    exact unroll nm e n lst tag r k flag index
  · intro flag index after hs
    rw [recorded_erases] at hs
    exact increment nm e n lst tag r k flag index after hs
  · omega
#print axioms erases
end R1Z.PV_L2_F6Null

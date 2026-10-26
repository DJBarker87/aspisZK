import R1Z.PV_L2_F6EchelonStep
set_option autoImplicit false
namespace R1Z.PV_L2_F6Echelon
open Aeneas Aeneas.Std Result R1CertCheck R1Z.PV_L2_Record
open R1Z.PV_L2_F6EchelonStep
def recorded 
  (e : Slice Std.U32) (n : Std.Usize) (lst : Slice Std.U32) (r : Std.Usize) : Recorded Bool :=
  PV_L2_F6FlagLoop.loop 21 (PV_L2_F6EchelonStep.recorded e n lst r) r r.val true 0#usize
theorem erases 
  (e : Slice Std.U32) (n : Std.Usize) (lst : Slice Std.U32) (r : Std.Usize) :
    (recorded e n lst r).value = ech_ok e n lst r := by
  unfold recorded
  apply PV_L2_F6FlagLoop.erases 21 (PV_L2_F6EchelonStep.recorded e n lst r) r (ech_ok_loop e n lst r)
  · intro flag index
    rw [recorded_erases]
    exact unroll e n lst r flag index
  · intro flag index after hs
    rw [recorded_erases] at hs
    exact increment e n lst r flag index after hs
  · omega
#print axioms erases
end R1Z.PV_L2_F6Echelon

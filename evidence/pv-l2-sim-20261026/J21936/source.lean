import R1Z.PV_L2_F6EchelonRowStep
set_option autoImplicit false
namespace R1Z.PV_L2_F6EchelonRow
open Aeneas Aeneas.Std Result R1CertCheck R1Z.PV_L2_Record
open R1Z.PV_L2_F6EchelonRowStep

def recorded 
  (e : Slice Std.U32) (n : Std.Usize) (lst : Slice Std.U32) (a : Std.Usize)
  (r : Std.Usize) : Recorded Bool :=
  PV_L2_F6FlagLoop.loop 11 (PV_L2_F6EchelonRowStep.recorded e n lst a r) r r.val true 0#usize

theorem erases 
  (e : Slice Std.U32) (n : Std.Usize) (lst : Slice Std.U32) (a : Std.Usize)
  (r : Std.Usize) :
    (recorded e n lst a r).value = ech_row_ok e n lst a r := by
  unfold recorded
  apply PV_L2_F6FlagLoop.erases 11 (PV_L2_F6EchelonRowStep.recorded e n lst a r) r
    (ech_row_ok_loop e n lst a r)
  · intro flag index
    rw [PV_L2_F6EchelonRowStep.recorded_erases]
    exact unroll e n lst a r flag index
  · intro flag index after hs
    rw [PV_L2_F6EchelonRowStep.recorded_erases] at hs
    exact increment e n lst a r flag index after hs
  · omega

#print axioms erases
end R1Z.PV_L2_F6EchelonRow

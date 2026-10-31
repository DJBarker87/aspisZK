import R1Z.PV_RunJoin_PostEquation60
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SliceCopy64
open Aeneas Aeneas.Std Result

theorem value {T : Type} (copy : core.marker.Copy T) (dst src out : Slice T)
    (success : core.slice.Slice.copy_from_slice copy dst src=ok out) : out=src := by
  unfold core.slice.Slice.copy_from_slice at success
  split at success
  · exact Result.ok.inj success.symm
  · cases success

#print axioms value
end R1Z.PV_RunJoin_SliceCopy64

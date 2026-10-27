import R1Z.PV_CBL_PopSlices
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PopSliceCases
set_option autoImplicit false
/-- Copy is a marker in this extraction: no clone or field arithmetic is called. -/
theorem marker_irrelevant {T : Type} (first second : core.marker.Copy T)
    (v : Slice T) (out : alloc.vec.Vec T) :
    PV_CBL_PopSlices.pop_slices_reference first v out =
      PV_CBL_PopSlices.pop_slices_reference second v out := rfl
theorem empty {T : Type} (copy : core.marker.Copy T) (v : Slice T) (out : alloc.vec.Vec T)
    (h : Slice.len v=0#usize) :
    PV_CBL_PopSlices.pop_slices_reference copy v out=ok (none,out) := by
  simp only [PV_CBL_PopSlices.pop_slices_reference,h,if_true]
#print axioms marker_irrelevant
#print axioms empty
end R1Z.PV_CBL_PopSliceCases

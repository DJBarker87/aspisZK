import R1Z.PV_CBL_ArraySliceLaw
import R1Z.PV_CBL_ArrayResult
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ArraySliceBridge
set_option autoImplicit false
/-- Binds the previous complete QM31 Result value adapter to the new extracted
borrowed-Slice wrapper. Native Copy/Clone, owned Vec and N=1024 association remain P. -/
theorem source (v : alloc.vec.Vec PV_CBL_ArrayQM31.Q) :
    PV_CBL_ArraySliceResult.array_slice_result_reference 1024#usize PV_CBL_ArrayQM31.marker
      (alloc.vec.Vec.deref v) PV_CBL_ArrayQM31.zero = PV_CBL_ArrayResult.reference v := by
  change PV_CBL_ArraySliceResult.array_slice_result_reference 1024#usize
    (PV_CBL_ArraySliceLaw.marker PV_CBL_ArrayQM31.Q) (alloc.vec.Vec.deref v) PV_CBL_ArrayQM31.zero = _
  rw [PV_CBL_ArraySliceLaw.source]
  by_cases h : alloc.vec.Vec.len v=1024#usize
  · obtain ⟨a,ha,hav⟩ := PV_CBL_ArrayResult.success v h
    rw [ha]
    have hs : Slice.len (alloc.vec.Vec.deref v)=1024#usize := h
    simp only [PV_CBL_ArraySliceLaw.value,dif_pos hs]
    apply congrArg ok
    apply congrArg core.result.Result.Ok
    apply Subtype.ext
    exact hav.symm
  · rw [PV_CBL_ArrayResult.reject v h]
    have hs : Slice.len (alloc.vec.Vec.deref v)≠1024#usize := h
    simp only [PV_CBL_ArraySliceLaw.value,dif_neg hs]
    rfl
#print axioms source
end R1Z.PV_CBL_ArraySliceBridge

import R1Z.PV_CBL_ArraySuccess
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ArrayDeterminism
set_option autoImplicit false

/-- The initialization element is observationally absent after all cells have
been copied. This does not evaluate a concrete large array. -/
theorem zero_independent {T : Type} (N : Usize) (copy : core.marker.Copy T)
    (v : Slice T) (zero other : T) :
    PV_CBL_ArrayKernel.array_reference N copy v zero =
      PV_CBL_ArrayKernel.array_reference N copy v other := by
  by_cases h : Slice.len v=N
  · obtain ⟨a,ha,hav⟩ := PV_CBL_ArraySuccess.success N copy v zero h
    obtain ⟨b,hb,hbv⟩ := PV_CBL_ArraySuccess.success N copy v other h
    have eq : a=b := Subtype.ext (hav.trans hbv.symm)
    rw [ha,hb,eq]
  · rw [PV_CBL_ArrayGuard.wrong_length N copy v zero h,
        PV_CBL_ArrayGuard.wrong_length N copy v other h]
#print axioms zero_independent
end R1Z.PV_CBL_ArrayDeterminism

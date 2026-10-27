import R1Z.PV_CBL_ArrayKernel
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ArrayGuard
set_option autoImplicit false

theorem wrong_length {T : Type} (N : Usize) (copy : core.marker.Copy T)
    (v : Slice T) (zero : T) (h : Slice.len v ≠ N) :
    PV_CBL_ArrayKernel.array_reference N copy v zero = ok none := by
  simp [PV_CBL_ArrayKernel.array_reference,h]

theorem correct_length {T : Type} (N : Usize) (copy : core.marker.Copy T)
    (v : Slice T) (zero : T) (h : Slice.len v = N) :
    PV_CBL_ArrayKernel.array_reference N copy v zero =
      (do let out ← PV_CBL_ArrayKernel.array_reference_loop v (Array.repeat N zero) 0#usize
          ok (some out)) := by
  simp [PV_CBL_ArrayKernel.array_reference,h]
#print axioms wrong_length
#print axioms correct_length
end R1Z.PV_CBL_ArrayGuard

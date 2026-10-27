import R1Z.PV_CBL_ArrayGuard
import R1Z.PV_CBL_ArrayCopied
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ArrayReferenceTotal
set_option autoImplicit false

/-- Every input returns a value; the length mismatch is preserved as None. -/
theorem total {T : Type} [Inhabited T] (N : Usize) (copy : core.marker.Copy T)
    (v : Slice T) (zero : T) :
    ∃ a, PV_CBL_ArrayKernel.array_reference N copy v zero = ok a := by
  by_cases h : Slice.len v=N
  · rw [PV_CBL_ArrayGuard.correct_length N copy v zero h]
    have hv : N.val≤v.val.length := by rw [←h]; rfl
    obtain ⟨a,ha,_⟩ := PV_CBL_ArrayCopied.total_copied v hv (Array.repeat N zero)
      0#usize (by simp) (PV_CBL_ArrayPrefix.initial _ _)
    exact ⟨some a,by rw [ha,bind_tc_ok]⟩
  · exact ⟨none,PV_CBL_ArrayGuard.wrong_length N copy v zero h⟩

/-- The reference's rejection branch is exactly the input-length test. -/
theorem none_iff {T : Type} [Inhabited T] (N : Usize) (copy : core.marker.Copy T)
    (v : Slice T) (zero : T) :
    PV_CBL_ArrayKernel.array_reference N copy v zero = ok none ↔ Slice.len v≠N := by
  constructor
  · intro ho h
    rw [PV_CBL_ArrayGuard.correct_length N copy v zero h] at ho
    have hv : N.val≤v.val.length := by rw [←h]; rfl
    obtain ⟨a,ha,_⟩ := PV_CBL_ArrayCopied.total_copied v hv (Array.repeat N zero)
      0#usize (by simp) (PV_CBL_ArrayPrefix.initial _ _)
    rw [ha,bind_tc_ok] at ho
    cases ho
  · exact PV_CBL_ArrayGuard.wrong_length N copy v zero
#print axioms total
#print axioms none_iff
end R1Z.PV_CBL_ArrayReferenceTotal

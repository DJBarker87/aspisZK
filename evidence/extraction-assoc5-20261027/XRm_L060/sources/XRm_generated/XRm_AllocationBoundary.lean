import XRk_CheckpointModel
open Aeneas Aeneas.Std Result
open XRk_Release
namespace XRm_AllocationBoundary
/-- The supplied heap model contains no allocation failure at any typed Usize.
This identifies the native allocator boundary; it is not a native totality law. -/
theorem filled_ne_error {T : Type} (copy : core.marker.Copy T) (n : Usize) (v : T) :
    aspis_core.r0.heap.filled copy n v ≠ ok (.Err aspis_core.r0.Error.Allocation) := by
  unfold aspis_core.r0.heap.filled
  rw [dif_pos (by scalar_tac)]
  intro h
  cases h
#print axioms filled_ne_error
end XRm_AllocationBoundary

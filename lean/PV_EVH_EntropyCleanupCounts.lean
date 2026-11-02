import PV_EVH_EntropyRejectCleanup
set_option autoImplicit false
namespace PV_EVH_EntropyCleanupCounts
open PV_EVH_StackZero (Slot State drop)

theorem drop_counts (slot : Slot) (w : State) :
    (drop slot w).writes = w.writes+slot.initialized ∧
    (drop slot w).barriers = w.barriers+slot.initialized ∧
    (drop slot w).drops = w.drops+1 := by
  have h := PV_EVH_DeployedZeroWorld.counts slot.address slot.initialized w
  have hf := PV_EVH_DeployedZeroWorld.frame slot.address slot.initialized w
  unfold drop PV_EVH_StackZero.retire
  rw [PV_EVH_DeployedZeroCursor.source]
  exact ⟨h.1,h.2,congrArg (fun n => n+1) hf.2.2.2.2⟩

/-- Deployed1.9.0's write AND per-byte barrier law feeds the rejected source
scope without expanding a 128-element recurrence. Frame provenance is not a
consequence of these counts, and no register/spill erasure is asserted. -/
theorem rejected_counts (original field seed : Slot) (w : State)
    (ho : original.initialized = 64) (hf : field.initialized = 32)
    (hs : seed.initialized = 32) :
    (PV_EVH_EntropyRejectCleanup.cleanup original field seed w).writes = w.writes+128 ∧
    (PV_EVH_EntropyRejectCleanup.cleanup original field seed w).barriers = w.barriers+128 ∧
    (PV_EVH_EntropyRejectCleanup.cleanup original field seed w).drops = w.drops+3 := by
  have a := drop_counts seed w
  have b := drop_counts field (drop seed w)
  have c := drop_counts original (drop field (drop seed w))
  unfold PV_EVH_EntropyRejectCleanup.cleanup
  omega

#print axioms drop_counts
#print axioms rejected_counts
end PV_EVH_EntropyCleanupCounts

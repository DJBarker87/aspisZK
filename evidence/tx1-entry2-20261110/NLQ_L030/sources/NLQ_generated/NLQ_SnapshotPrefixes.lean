import NLQ_SnapshotFold
set_option autoImplicit false
noncomputable section
namespace NLQ_SnapshotPrefixes
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry NLM_Snapshot
/-- The FIRST allocation abort has its live shared token in the retained
prefix; no second/third snapshot or cleanup is invented after it. -/
theorem first_abort (e : Entry) (err : Aeneas.Std.Error) (a1 a2 : Result Unit)
 (extent : (S2W_ReturnedCheckpoint.nativeBytes (e.buffers (e.handles 0).1)).length=58295) :
 NLQ_SnapshotFold.G e (.fail err) a1 a2 =
 ⟨.fail err,allocationPrefix (ready e 0 []) 0 (.fail err)⟩ := by
 unfold NLQ_SnapshotFold.G
 rw [NLM_Snapshot.allocation_abort e 0 0 58295 58295 [] err (Or.inl extent)]
 rfl
theorem first_diverge (e : Entry) (a1 a2 : Result Unit)
 (extent : (S2W_ReturnedCheckpoint.nativeBytes (e.buffers (e.handles 0).1)).length=58295) :
 NLQ_SnapshotFold.G e .div a1 a2 =
 ⟨.div,allocationPrefix (ready e 0 []) 0 .div⟩ := by
 unfold NLQ_SnapshotFold.G
 rw [NLM_Snapshot.allocation_diverge e 0 0 58295 58295 [] (Or.inl extent)]
 rfl
#check @first_abort
#check @first_diverge
#print axioms first_abort
#print axioms first_diverge
end NLQ_SnapshotPrefixes

import NLQ_SnapshotFold
set_option autoImplicit false
noncomputable section
namespace NLQ_SnapshotSkip
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry NLM_Snapshot NLF_SdkModel
/-- Malformed extents defer an owned byte error WITHOUT invoking allocation.
An unrelated allocator failure must not remove this returning error path. -/
theorem skip (e : Entry) (t a lo hi : Nat) (owned : List NLM_Snapshot.Owned)
 (allocation : Result Unit)
 (bad : ¬ ((S2W_ReturnedCheckpoint.nativeBytes (e.buffers (e.handles a).1)).length=lo ∨
          (S2W_ReturnedCheckpoint.nativeBytes (e.buffers (e.handles a).1)).length=hi)) :
 NLM_Snapshot.G (ready e t owned) a lo hi allocation =
 NLM_Snapshot.G (ready e t owned) a lo hi (.ok ()) := by
 unfold NLM_Snapshot.G
 rw [NLM_Snapshot.acquire]
 have disallowed := bad
 rw [←NLM_Snapshot.current_payload e t a owned] at disallowed
 simp only [NLM_Snapshot.acquired,NLM_Snapshot.guard,shared_deref] at disallowed
 simp [disallowed,Bind.bind,Pure.pure,NJU_Log.bind,NJU_Log.record,
  NLM_Snapshot.acquired,NLM_Snapshot.guard,shared_deref]
#print axioms skip
end NLQ_SnapshotSkip

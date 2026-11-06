import NLM_SnapshotSkip
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
 NLM_Snapshot.G (ready e t owned) a lo hi (.ok ()) :=
 NLM_Snapshot.skip_allocation e t a lo hi owned allocation bad

#print axioms skip
end NLQ_SnapshotSkip

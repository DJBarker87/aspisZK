import NLQ_SnapshotReplay
set_option autoImplicit false
noncomputable section
namespace NLQ_ReplayNormal
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry NLM_Snapshot
/-- The returning snapshot's event chain restores the SAME complete SDK
state and advances ownership and token allocation exactly once. -/
theorem normal (e : Entry) (t a lo hi : Nat) (owned : List NLM_Snapshot.Owned) :
 NLQ_SnapshotReplay.replay (ready e t owned)
  (NLM_Snapshot.G (ready e t owned) a lo hi (.ok ())).events=
 NLM_Snapshot.returned (ready e t owned) a lo hi := by
 unfold NLM_Snapshot.G
 rw [NLM_Snapshot.acquire]
 simp [Bind.bind,Pure.pure,NJU_Log.bind,NJU_Log.record,NLM_Snapshot.release_current,
  NLQ_SnapshotReplay.replay,NLQ_SnapshotReplay.step,NLM_Snapshot.returned,NLM_Snapshot.live]
#print axioms normal
end NLQ_ReplayNormal

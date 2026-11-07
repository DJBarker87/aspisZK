import NMB_SnapshotReturn
set_option autoImplicit false
noncomputable section
namespace NMB_SnapshotTrace
open Aeneas Aeneas.Std Result AspisR1 NMB_Snapshot
/-- Completed normal snapshot chronology. The conditional event is the
source to_vec occurrence, not an invented allocation on malformed extents. -/
def events (s : State) (a lo hi : Nat) : List Event :=
 let g := NMB_Snapshot.guard s a
 let payload := NLF_SdkModel.deref (acquired s a) g
 [.acquire s a s.next (acquired s a) (.ok (.ok g)),
  .deref (NMB_Snapshot.live s a) g (.ok payload)] ++
 (if payload.bytes.length=lo ∨ payload.bytes.length=hi then
  [.allocate (NMB_Snapshot.live s a) g payload.bytes.length (.ok ())] else []) ++
 [.release (NMB_Snapshot.live s a) g (.ok (.ok s.sdk)),
  .returned (NMB_Snapshot.live s a) a lo hi (.ok (s.input.snapshot a lo hi))]
theorem source (x : NMB_Input.Input) (t a lo hi : Nat) (owned : List Owned) :
 (G (ready x t owned) a lo hi (.ok ())).events=events (ready x t owned) a lo hi := by
 unfold G
 rw [NMB_SnapshotAcquire.acquire]
 have released := NMB_SnapshotAcquire.release x t a owned
 simp only [Bind.bind,Pure.pure,NJU_Log.bind,NJU_Log.record]
 split <;> simp_all [events,Bind.bind,Pure.pure,NJU_Log.bind,NJU_Log.record,
   NMB_Snapshot.live,NMB_Snapshot.guard,acquired]
#print source
#print axioms source
end NMB_SnapshotTrace

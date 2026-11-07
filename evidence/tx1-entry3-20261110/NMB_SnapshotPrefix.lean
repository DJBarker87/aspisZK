import NMB_SnapshotAcquire
set_option autoImplicit false
noncomputable section
namespace NMB_SnapshotPrefix
open Aeneas Aeneas.Std Result AspisR1 NLF_RefCell NLF_SdkModel NMB_Snapshot
/-- The live guard at the allocator call. No release/returned event is
invented when the actual allocator aborts or diverges at this point. -/
def allocationEvents (s : NMB_Snapshot.State) (a : Nat) (allocation : Result Unit) : List Event :=
 [ .acquire s a s.next (acquired s a) (.ok (.ok (NMB_Snapshot.guard s a))),
   .deref (NMB_Snapshot.live s a) (NMB_Snapshot.guard s a) (.ok (deref (acquired s a) (NMB_Snapshot.guard s a))),
   .allocate (NMB_Snapshot.live s a) (NMB_Snapshot.guard s a)
     (deref (acquired s a) (NMB_Snapshot.guard s a)).bytes.length allocation]
theorem failure (x : NMB_Input.Input) (t a lo hi : Nat) (owned : List Owned)
 (e : Aeneas.Std.Error) (extent : (S2W_ReturnedCheckpoint.nativeBytes
   (x.buffers (x.handles a).1)).length=lo ∨
   (S2W_ReturnedCheckpoint.nativeBytes (x.buffers (x.handles a).1)).length=hi) :
 G (ready x t owned) a lo hi (.fail e) =
 ⟨.fail e,allocationEvents (ready x t owned) a (.fail e)⟩ := by
 unfold G
 rw [NMB_SnapshotAcquire.acquire]
 have allowed := extent
 rw [←NMB_SnapshotAcquire.payload x t a owned] at allowed
 simp only [acquired,NMB_Snapshot.guard,shared_deref] at allowed
 simp [allowed,Bind.bind,Pure.pure,NJU_Log.bind,NJU_Log.record,allocationEvents,NMB_Snapshot.live,NMB_Snapshot.guard,acquired,shared_deref]
theorem divergence (x : NMB_Input.Input) (t a lo hi : Nat) (owned : List Owned)
 (extent : (S2W_ReturnedCheckpoint.nativeBytes
   (x.buffers (x.handles a).1)).length=lo ∨
   (S2W_ReturnedCheckpoint.nativeBytes (x.buffers (x.handles a).1)).length=hi) :
 G (ready x t owned) a lo hi .div =
 ⟨.div,allocationEvents (ready x t owned) a .div⟩ := by
 unfold G
 rw [NMB_SnapshotAcquire.acquire]
 have allowed := extent
 rw [←NMB_SnapshotAcquire.payload x t a owned] at allowed
 simp only [acquired,NMB_Snapshot.guard,shared_deref] at allowed
 simp [allowed,Bind.bind,Pure.pure,NJU_Log.bind,NJU_Log.record,allocationEvents,NMB_Snapshot.live,NMB_Snapshot.guard,acquired,shared_deref]
#print failure
#print divergence
#print axioms failure
#print axioms divergence
end NMB_SnapshotPrefix

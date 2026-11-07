import NMB_SnapshotAcquire
set_option autoImplicit false
noncomputable section
namespace NMB_SnapshotSkip
open Aeneas Aeneas.Std Result AspisR1 NMB_Snapshot NLF_SdkModel
theorem skip (x : NMB_Input.Input) (t a lo hi : Nat) (owned : List Owned)
 (allocation : Result Unit)
 (bad : ¬ ((S2W_ReturnedCheckpoint.nativeBytes (x.buffers (x.handles a).1)).length=lo ∨
   (S2W_ReturnedCheckpoint.nativeBytes (x.buffers (x.handles a).1)).length=hi)) :
 G (ready x t owned) a lo hi allocation = G (ready x t owned) a lo hi (.ok ()) := by
 unfold G
 rw [NMB_SnapshotAcquire.acquire]
 have reject := bad
 rw [←NMB_SnapshotAcquire.payload x t a owned] at reject
 simp only [acquired,NMB_Snapshot.guard,shared_deref] at reject
 simp [reject,Bind.bind,Pure.pure,NJU_Log.bind,NJU_Log.record,NMB_Snapshot.live,NMB_Snapshot.guard,acquired,shared_deref]
#print skip
#print axioms skip
end NMB_SnapshotSkip

import NLM_SnapshotAcquire
set_option autoImplicit false
noncomputable section
namespace NLM_Snapshot
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry NLF_RefCell NLF_SdkModel
/-- Up to the allocation call, the shared token is live in the SAME cell. -/
def allocationPrefix (s : State) (a : Nat) (allocation : Result Unit) : List Event :=
 [.acquire s a s.next (acquired s a) (.ok (.ok (guard s a))),
  .deref (live s a) (guard s a) (.ok (deref (acquired s a) (guard s a))),
  .allocate (live s a) (guard s a) (deref (acquired s a) (guard s a)).bytes.length allocation]
theorem allocation_abort (e : Entry) (t a lo hi : Nat) (owned : List Owned) (err : Aeneas.Std.Error)
 (copy : (AspisR1.S2W_ReturnedCheckpoint.nativeBytes (e.buffers (e.handles a).1)).length=lo ∨
         (AspisR1.S2W_ReturnedCheckpoint.nativeBytes (e.buffers (e.handles a).1)).length=hi) :
 G (ready e t owned) a lo hi (.fail err)=
 ⟨.fail err,allocationPrefix (ready e t owned) a (.fail err)⟩ := by
 unfold G
 rw [acquire]
 have allowed := copy
 rw [←current_payload e t a owned] at allowed
 simp only [acquired,guard,shared_deref] at allowed
 simp [allowed,Bind.bind,Pure.pure,NJU_Log.bind,NJU_Log.record,allocationPrefix,live,guard,acquired,shared_deref]
theorem allocation_diverge (e : Entry) (t a lo hi : Nat) (owned : List Owned)
 (copy : (AspisR1.S2W_ReturnedCheckpoint.nativeBytes (e.buffers (e.handles a).1)).length=lo ∨
         (AspisR1.S2W_ReturnedCheckpoint.nativeBytes (e.buffers (e.handles a).1)).length=hi) :
 G (ready e t owned) a lo hi .div=
 ⟨.div,allocationPrefix (ready e t owned) a .div⟩ := by
 unfold G
 rw [acquire]
 have allowed := copy
 rw [←current_payload e t a owned] at allowed
 simp only [acquired,guard,shared_deref] at allowed
 simp [allowed,Bind.bind,Pure.pure,NJU_Log.bind,NJU_Log.record,allocationPrefix,live,guard,acquired,shared_deref]
#print allocation_abort
#print allocation_diverge
#print axioms allocation_abort
#print axioms allocation_diverge
end NLM_Snapshot

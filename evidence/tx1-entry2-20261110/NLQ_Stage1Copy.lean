import NLQ_SnapshotFrame
import NLQ_CopyTrace
set_option autoImplicit false
noncomputable section
namespace NLQ_Stage1Copy
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry
open NLF_RefCell NLF_SdkModel
/-- Exact checkpoint write on the state returned by the three source
snapshots. src must be the SAME child-produced value; this own-input length
clause still has to be discharged by stage1_owned at its actual occurrence. -/
theorem copy (e : Entry) (src : List UInt8)
 (same : src.length=(S2W_ReturnedCheckpoint.nativeBytes (e.buffers (e.handles 2).1)).length) :
 let s := (NLQ_SnapshotFold.final e).sdk
 (NLQ_CopyTrace.G s 2 3 src).outcome = .returned
  (put s (s.accounts 2).data {s.cells (s.accounts 2).data with
   payload:={(s.cells (s.accounts 2).data).payload with bytes:=src}}) (.ok ()) := by
 dsimp only
 rw [NLQ_CopyTrace.erasure]
 apply NLF_CopyStep.success
 · rfl
 · rfl
 · rw [NLQ_SnapshotFrame.current_payload]
   exact same
/-- If the child's length clause is violated, the source's unchecked
copy_from_slice aborts while the exclusive token is live. No Drop suffix. -/
theorem wrong_length (e : Entry) (src : List UInt8)
 (bad : src.length≠(S2W_ReturnedCheckpoint.nativeBytes (e.buffers (e.handles 2).1)).length) :
 let s := (NLQ_SnapshotFold.final e).sdk
 (NLQ_CopyTrace.G s 2 3 src).outcome = .abort
  (put s (s.accounts 2).data {s.cells (s.accounts 2).data with writer:=some 3}) := by
 dsimp only
 rw [NLQ_CopyTrace.erasure]
 apply NLF_CopyStep.wrong_length
 · rfl
 · rfl
 · rw [NLQ_SnapshotFrame.current_payload]
   exact bad
#check @copy
#check @wrong_length
#print axioms copy
#print axioms wrong_length
end NLQ_Stage1Copy

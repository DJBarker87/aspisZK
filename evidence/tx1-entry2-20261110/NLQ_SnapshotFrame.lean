import NLQ_SnapshotFold
set_option autoImplicit false
noncomputable section
namespace NLQ_SnapshotFrame
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry
/-- Frame of the SAME returned snapshot chain, not an independently chosen
post-state. This is source/std support; allocation admission is still separate. -/
theorem source_frame (e : Entry) :
 (do let pair ← (NLQ_SnapshotFold.G e (.ok ()) (.ok ()) (.ok ())).result
     ok (pair.1,pair.2.sdk,pair.2.next,pair.2.owned)) =
 .ok (e.first,(NLM_RuntimeInput.initial e).state,3,
  [e.snapshot 0 58295 58295,e.snapshot 1 1880 1880,e.snapshot 2 1768 1768]) := by
 rw [NLQ_SnapshotFold.returned]
 rfl
/-- All original bytes and current account handles come from the SAME input;
no equality of addresses is used to infer this payload law. -/
theorem current_payload (e : Entry) (account : Nat) :
 (((NLQ_SnapshotFold.final e).sdk).cells
   (((NLQ_SnapshotFold.final e).sdk).accounts account).data).payload.bytes =
 S2W_ReturnedCheckpoint.nativeBytes (e.buffers (e.handles account).1) :=
 NLM_RuntimeInput.initial_payload e account
/-- Admission facts are consumed on the exact runtime installation used by
this source chain, rather than a separately chosen counter/cell map. -/
theorem admitted (e : Entry)
 (runtime : AdapterRw.RuntimeEntrypointAdmission e.heap
   (fun a => (NLM_RuntimeInput.records e a).key) 3) :
 (∀ a, a<3 → e.heap.ownerLive a=true) ∧
 (∀ i, NLF_RefCell.flag ((NLQ_SnapshotFold.final e).sdk.cells i)=e.heap.counter i) := by
 have h := NLF_SdkBorrowLaw.admitted_events e.heap (NLM_RuntimeInput.records e)
  (NLM_RuntimeInput.money e) 3 runtime []
 exact ⟨h.2.2,h.2.1⟩
#check @source_frame
#check @current_payload
#check @admitted
#print axioms source_frame
#print axioms current_payload
#print axioms admitted
end NLQ_SnapshotFrame

import PoolT_Verifier
import Hir_CallSuccess
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolT_Write
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_TrustedStd S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory
open MultiproofConeCanonical Hist_Store Hist_RuntimeEntry

/-- Accepted verifier TX1 writes its own returned vector at its actual account2
cell, with full heap/metadata/other-cell frames. The saved size, copy output,
release and cleanup equations are conclusions of this same invocation.
The adopted extraction/SDK/std/runtime interpretations remain explicit. -/
theorem accepted_verifier_writes_copy {A : Type} (ops : AdapterRw.Ops)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction ops native1 native2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A) (e : Entry)
    (program : S2W_ExtractionBoundary.Program) (data : Slice U8) (state final : A)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record))
    (accepted : first native1 copy allocator e program data state = ok (.Ok (saved,post,final))) :
    native1 program e.first data = ok (.Ok saved) ∧
    saved.val.length = 1768 ∧
    payloadBytes encode (post.payload (e.heap.accounts 2).1) 1768 = bytesOf saved.val ∧
    post.ambient = e.heap.ambient ∧ post.accounts = e.heap.accounts ∧
    post.counter = e.heap.counter ∧
    (∀ cell, cell ≠ (e.heap.accounts 2).1 → post.payload cell = e.heap.payload cell) := by
  obtain ⟨native,written⟩ := first_accepted native1 copy std allocator e program data state final saved post accepted
  have sourceAccepted := (extraction.stage1 program e.first data).symm.trans native
  have size := PoolT_Verifier.returned_size ops e program data saved sourceAccepted
  have destination := checkpoint_size e ops program data saved sourceAccepted
  have frame := checkpoint_write e.heap 2 0 0 (source (nativeBytes saved)) rfl rfl destination
  refine ⟨native,size,Hist_CommittedPayload.copied ops native1 native2 hashv extraction
    copy std allocator e program data state final saved post accepted size,?_,?_,?_,?_⟩
  · rw [written]; exact frame.2.1
  · rw [written]; exact frame.2.2.1
  · rw [written]; exact frame.2.2.2.1
  · rw [written]; exact frame.2.2.2.2

/-- The canonical call effect uses this invocation's physical account key and
returned bytes. This is a local call/commit interpretation, not a proof of
runtime genesis, scheduler, deployment, rollback or cross-transaction retention. -/
theorem accepted_verifier_event {A : Type}
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (allocator : Allocator A) (program : S2W_ExtractionBoundary.Program)
    (store : Hist_Store.Store) (call : Hir_Call.Call A)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (route : Hiq_ReleaseRoute.route call.data = .first)
    (accepted : first native1 copy allocator (load store call.layout) program call.data call.state =
      ok (.Ok (saved,post,final))) :
    Hir_Call.native native1 native2 copy allocator program store call =
      (commit store (call.layout.handles 2).1 saved,
        .committedWrite (call.layout.handles 2).1 (bytesOf saved.val),
        .inl (.ok (.Ok (saved,post,final)))) :=
  Hir_CallSuccess.effect native1 native2 copy allocator program store call saved post final route accepted

#print axioms accepted_verifier_writes_copy
#print axioms accepted_verifier_event
end AspisR1.PoolT_Write
end

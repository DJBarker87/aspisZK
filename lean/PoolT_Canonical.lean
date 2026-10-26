import PoolT_Write
import Hiq_NativeWriter
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolT_Canonical
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_TrustedStd S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory
open MultiproofConeCanonical Hist_Store Hist_RuntimeEntry

/-- Same complete native reply fixes both local copy and local ledger event.
No independent key, payload or post-account observation is an input. -/
theorem verifier {A : Type} (ops : AdapterRw.Ops)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction ops native1 native2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (program : S2W_ExtractionBoundary.Program) (store : Store) (layout : Layout)
    (data : Slice U8) (state final : A) (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record))
    (accepted : first native1 copy allocator (load store layout) program data state = ok (.Ok (saved,post,final))) :
    Hiq_NativeWriter.apply native1 copy allocator program store layout data state =
      (commit store (layout.handles 2).1 saved,
        .committedWrite (layout.handles 2).1 (bytesOf saved.val)) ∧
    payloadBytes encode (post.payload (layout.handles 2).1) 1768 = bytesOf saved.val ∧
    saved.val.length = 1768 := by
  have copied := PoolT_Write.accepted_verifier_writes_copy ops native1 native2 hashv extraction
    copy std allocator (load store layout) program data state final saved post accepted
  refine ⟨?_,copied.2.2.1,copied.2.1⟩
  simp only [Hiq_NativeWriter.apply,accepted]

#print axioms verifier
end AspisR1.PoolT_Canonical
end

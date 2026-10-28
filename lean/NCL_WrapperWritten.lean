import NCL_WrapperLength
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCL_WrapperWritten
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_TrustedStd S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws
open S2W_EntryWriteHistory MultiproofConeCanonical

/-- Same returned checkpoint, exact1768 saved bytes and model account frame,
derived from wrapper acceptance and its existing std/runtime contracts.
This is NOT the actual native snapshot/copy/cleanup association. -/
theorem source {A : Type} (native : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A) (e : Entry)
    (program : S2W_ExtractionBoundary.Program) (data : Slice U8) (state final : A)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record))
    (empty : e.heap.guards = []) (zero : e.heap.counter (e.heap.accounts 2).1 = 0)
    (destination : (e.heap.payload (e.heap.accounts 2).1).descriptor.length = 1768)
    (accepted : first native copy allocator e program data state = ok (.Ok (saved,post,final))) :
    saved.val.length = 1768 ∧
    payloadBytes encode (post.payload (e.heap.accounts 2).1) 1768 = bytesOf saved.val ∧
    post.ambient = e.heap.ambient ∧ post.accounts = e.heap.accounts ∧
    post.counter = e.heap.counter ∧
    (∀ cell, cell ≠ (e.heap.accounts 2).1 → post.payload cell = e.heap.payload cell) := by
  have size := NCL_WrapperLength.source native copy std allocator e program data state final
    saved post destination accepted
  have write := (first_accepted native copy std allocator e program data state final saved post accepted).2
  refine ⟨size,?_,?_,?_,?_,?_⟩
  · rw [write,written_bytes encode e.heap 2 0 0 _ empty zero destination]
    have length : (nativeBytes saved).length = 1768 := by
      simpa only [nativeBytes,List.length_map] using size
    rw [←length,source_bytes,vector_representation]
  all_goals
    rw [write]
    have frame := checkpoint_write e.heap 2 0 0
      (S2W_CommittedCheckpoint.source (nativeBytes saved)) empty zero destination
    first | exact frame.2.1 | exact frame.2.2.1 | exact frame.2.2.2.1 | exact frame.2.2.2.2
#print axioms source
end AspisR1.NCL_WrapperWritten
end

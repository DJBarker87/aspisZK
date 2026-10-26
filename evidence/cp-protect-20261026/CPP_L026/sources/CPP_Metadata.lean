import PoolT_CopyShape
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_Metadata
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_TrustedStd S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory S2W_CommittedCheckpoint

/-- Accepted TX1 cannot close, resize, reassign, change lamports/metadata,
or leave a live mutable guard in the complete wrapper interpretation. -/
theorem first_frame {A : Type} (n1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A) (e : Entry)
    (id : S2W_ExtractionBoundary.Program) (data : Slice U8) (state final : A)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record))
    (accepted : first n1 copy allocator e id data state = ok (.Ok (saved,post,final))) :
    post.ambient = e.records ∧ post.accounts = e.handles ∧
    post.counter = e.heap.counter ∧ post.external = e.heap.external ∧
    post.guards = [] ∧ post.allocated = e.heap.allocated ∧ post.ownerLive = e.heap.ownerLive ∧
    (∀ cell, (post.payload cell).descriptor = (e.heap.payload cell).descriptor) ∧
    (∀ cell, cell ≠ (e.handles 2).1 → post.payload cell = e.heap.payload cell) := by
  have written := (first_accepted n1 copy std allocator e id data state final saved post accepted).2
  rw [written,write_bracket e.heap 2 0 0 (source (nativeBytes saved)) rfl rfl]
  exact copy_frame e.heap (e.heap.accounts 2).1 (source (nativeBytes saved))

/-- The readonly wrapper frames the full heap without any child-totality,
SDK, std-copy or extraction hypothesis. It may still change private allocator
state, return errors, or diverge. -/
theorem second_frame {A : Type} (n2 : S2W_ExtractionBoundary.Second)
    (allocator : Allocator A) (e : Entry) (id : S2W_ExtractionBoundary.Program)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (state final : A)
    (post : Heap (Nat → Record))
    (accepted : second n2 allocator e id data slot state = ok (.Ok (post,final))) : post = e.heap :=
  (second_accepted n2 allocator e id data slot state final post accepted).2

#print axioms first_frame
#print axioms second_frame
end AspisR1.CPP_Metadata
end

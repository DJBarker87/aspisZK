import NNE_WrapperReturn
set_option autoImplicit false
noncomputable section
namespace NNE_AbortIndicator
open Aeneas Aeneas.Std Result AspisR1 S2Trust S2W_D189Entry S2W_D189Wrappers
/-- Ruling (bo): instantiate the headline's data binder, adding no Prop. -/
def allocator : Allocator Bool where
 allocate b _ := if b then ok b else fail .assertionFailure
 cleanup b := if b then ok b else fail .assertionFailure

theorem reserve_true (sizes : List Nat) : reserve allocator sizes true = ok true := by
 induction sizes with
 | nil => rfl
 | cons n ns ih =>
  change S2W_Trace.thenResult (ok true) (fun b => reserve allocator ns b) = ok true
  exact ih

theorem cleanup_true : allocator.cleanup true = ok true := rfl

theorem reserve_false (n : Nat) (ns : List Nat) :
 reserve allocator (n :: ns) false = fail .assertionFailure := rfl

theorem first_return (native : S2W_ExtractionBoundary.First)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy) (e : Entry)
 (p : S2W_ExtractionBoundary.Program) (data : Slice U8) (saved : alloc.vec.Vec U8)
 (owned : native p e.first data = ok (.Ok saved))
 (length : (e.heap.payload (e.heap.accounts 2).1).descriptor.length =
  (S2W_CommittedCheckpoint.source (S2W_ReturnedCheckpoint.nativeBytes saved)).descriptor.length) :
 first native copy allocator e p data true = ok (.Ok (saved,
  S2W_WrapperLaws.writeBracket e.heap 2 0 0
   (S2W_CommittedCheckpoint.source (S2W_ReturnedCheckpoint.nativeBytes saved)),true)) :=
 NNE_WrapperReturn.first_return native copy std allocator e p data true true true saved
  (reserve_true _) owned length cleanup_true

theorem second_return (native : S2W_ExtractionBoundary.Second) (e : Entry)
 (p : S2W_ExtractionBoundary.Program) (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
 (owned : native p (e.second secondSizes) data slot = ok (.Ok ())) :
 second native allocator e p data slot true = ok (.Ok (e.heap,true)) :=
 NNE_WrapperReturn.second_return native allocator e p data slot true true true
  (reserve_true _) owned cleanup_true
#print axioms reserve_true
#print axioms cleanup_true
#print axioms reserve_false
#print axioms first_return
#print axioms second_return
end NNE_AbortIndicator
end

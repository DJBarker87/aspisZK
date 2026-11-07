import S2W_D189Wrappers
set_option autoImplicit false
noncomputable section
namespace NNE_WrapperReturn
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2Trust
open S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd S2W_WrapperLaws
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint
/-- A3 final assembly. These are intermediate cut equations, NOT an actual
wrapper root. The RSL/allocator/owned packets must derive every equation. -/
theorem first_return {A : Type} (native : S2W_ExtractionBoundary.First)
 (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
 (std : TrustedStd copy) (allocator : Allocator A) (e : Entry)
 (program : S2W_ExtractionBoundary.Program) (data : Slice U8)
 (initial allocated final : A) (saved : alloc.vec.Vec U8)
 (allocation : reserve allocator (admittedSizes e 3 firstSizes) initial = ok allocated)
 (owned : native program e.first data = ok (.Ok saved))
 (length : (e.heap.payload (e.heap.accounts 2).1).descriptor.length =
   (source (nativeBytes saved)).descriptor.length)
 (cleanup : allocator.cleanup allocated = ok final) :
 first native copy allocator e program data initial =
 ok (.Ok (saved,writeBracket e.heap 2 0 0 (source (nativeBytes saved)),final)) := by
 have copied := S2W_TrustedStd.accepted_copy copy std
   (acquire e.heap (e.heap.accounts 2).1 0 0 .exclusive) (e.heap.accounts 2).1
   (source (nativeBytes saved)) length
 simp only [first,allocation,owned,copied,cleanup,bind_tc_ok]
 rfl
/-- A4 final assembly retains the allocator's ACTUAL final state. -/
theorem second_return {A : Type} (native : S2W_ExtractionBoundary.Second)
 (allocator : Allocator A) (e : Entry)
 (program : S2W_ExtractionBoundary.Program) (data : Slice U8)
 (slot : S2W_ExtractionBoundary.Slot) (initial allocated final : A)
 (allocation : reserve allocator (admittedSizes e 7 secondSizes) initial = ok allocated)
 (owned : native program (e.second secondSizes) data slot = ok (.Ok ()))
 (cleanup : allocator.cleanup allocated = ok final) :
 second native allocator e program data slot initial = ok (.Ok (e.heap,final)) := by
 simp only [second,allocation,owned,cleanup,bind_tc_ok]
#print axioms first_return
#print axioms second_return
end NNE_WrapperReturn
end

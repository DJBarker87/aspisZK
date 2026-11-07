import NNE_WrapperReturn
set_option autoImplicit false
noncomputable section
namespace NNE_Allocator
open Aeneas Aeneas.Std Result AspisR1 S2Trust S2W_D189Entry S2W_D189Wrappers
/-- The row specs do not carry these private allocator transitions. Failure
must remain a stop; it cannot be inferred away from a relational Ok arm. -/
theorem first_allocation_failure {A : Type} (native : S2W_ExtractionBoundary.First)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (allocator : Allocator A) (e : Entry) (p : S2W_ExtractionBoundary.Program)
 (data : Slice U8) (s : A) (error : Error)
 (failed : reserve allocator (admittedSizes e 3 firstSizes) s = fail error) :
 first native copy allocator e p data s = fail error := by
 simp only [first,failed,bind_tc_fail]

theorem second_allocation_failure {A : Type} (native : S2W_ExtractionBoundary.Second)
 (allocator : Allocator A) (e : Entry) (p : S2W_ExtractionBoundary.Program)
 (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (s : A) (error : Error)
 (failed : reserve allocator (admittedSizes e 7 secondSizes) s = fail error) :
 second native allocator e p data slot s = fail error := by
 simp only [second,failed,bind_tc_fail]

theorem first_not_accepted_after_allocation_failure {A : Type}
 (native : S2W_ExtractionBoundary.First)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (allocator : Allocator A) (e : Entry) (p : S2W_ExtractionBoundary.Program)
 (data : Slice U8) (s final : A) (error : Error) (saved : alloc.vec.Vec U8)
 (post : Heap (Nat → Record))
 (failed : reserve allocator (admittedSizes e 3 firstSizes) s = fail error) :
 first native copy allocator e p data s ≠ ok (.Ok (saved,post,final)) := by
 rw [first_allocation_failure native copy allocator e p data s error failed]
 intro h; cases h

theorem second_not_accepted_after_allocation_failure {A : Type}
 (native : S2W_ExtractionBoundary.Second) (allocator : Allocator A) (e : Entry)
 (p : S2W_ExtractionBoundary.Program) (data : Slice U8)
 (slot : S2W_ExtractionBoundary.Slot) (s final : A) (error : Error)
 (post : Heap (Nat → Record))
 (failed : reserve allocator (admittedSizes e 7 secondSizes) s = fail error) :
 second native allocator e p data slot s ≠ ok (.Ok (post,final)) := by
 rw [second_allocation_failure native allocator e p data slot s error failed]
 intro h; cases h
#print axioms first_allocation_failure
#print axioms second_allocation_failure
#print axioms first_not_accepted_after_allocation_failure
#print axioms second_not_accepted_after_allocation_failure
end NNE_Allocator
end

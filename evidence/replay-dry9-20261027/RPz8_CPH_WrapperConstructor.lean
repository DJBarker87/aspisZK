import RPz8_CPH_FixtureReserve
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPH_WrapperConstructor
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_CommittedCheckpoint S2W_ReturnedCheckpoint S2W_WrapperLaws S2W_TrustedStd

theorem first_success {A : Type} (n1 : S2W_ExtractionBoundary.First)
    (allocator : Allocator A) (e : Entry) (id : S2W_ExtractionBoundary.Program)
    (data : Slice U8) (state allocated cleaned : A) (saved : alloc.vec.Vec U8)
    (reserved : reserve allocator (admittedSizes e 3 firstSizes) state = ok allocated)
    (called : n1 id e.first data = ok (.Ok saved))
    (cleanup : allocator.cleanup allocated = ok cleaned)
    (lengths : ((acquire e.heap (e.heap.accounts 2).1 0 0 .exclusive).payload (e.heap.accounts 2).1).descriptor.length =
      (source (nativeBytes saved)).descriptor.length) :
    first n1 specification allocator e id data state =
      ok (.Ok (saved,writeBracket e.heap 2 0 0 (source (nativeBytes saved)),cleaned)) := by
  simp [first,reserved,called,cleanup,specification,lengths,writeBracket]

#print axioms first_success
end AspisR1.CPH_WrapperConstructor
end

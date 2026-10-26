import S2W_D189Wrappers
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_Second
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers

/-- Complete result of the readonly native wrapper; errors and divergence are
preserved, and the native child is evaluated once. Allocator state is private. -/
theorem exact {A : Type} (native : S2W_ExtractionBoundary.Second)
    (allocator : Allocator A) (e : Entry) (id : S2W_ExtractionBoundary.Program)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (state : A) :
    second native allocator e id data slot state = (do
      let allocated ← reserve allocator (admittedSizes e 7 secondSizes) state
      let result ← native id (e.second secondSizes) data slot
      match result with
      | .Err error => ok (.Err error)
      | .Ok () => do
        let cleaned ← allocator.cleanup allocated
        ok (.Ok (e.heap,cleaned))) := rfl

#print axioms exact
end AspisR1.CPP_Second
end

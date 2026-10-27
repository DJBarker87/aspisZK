import S2W_D189Wrappers
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_SecondWrapper
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers

/-- Allocation and cleanup stay explicit. This is a generic forward wrapper
lemma and supplies no native success witness by itself. -/
theorem source {A : Type} (native : S2W_ExtractionBoundary.Second) (allocator : Allocator A)
    (entry : Entry) (program : S2W_ExtractionBoundary.Program) (data : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (initial allocated final : A)
    (allocation : reserve allocator (admittedSizes entry 7 secondSizes) initial=ok allocated)
    (call : native program (entry.second secondSizes) data slot=ok (.Ok ()))
    (cleanup : allocator.cleanup allocated=ok final) :
    second native allocator entry program data slot initial=ok (.Ok (entry.heap,final)) := by
  unfold second
  rw [allocation,bind_tc_ok,call,bind_tc_ok,cleanup,bind_tc_ok]
#print axioms source
end AspisR1.JGx_SecondWrapper
end

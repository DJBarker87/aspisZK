import JHf_NativeRefutation
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHf_TX2
open Aeneas Aeneas.Std Result DrvC_Installation S2W_D189Wrappers S2Trust

theorem not_accepted2 {A C : Type} (c : Configuration FIo_Install.W C) (err : C)
    (allocator : Allocator A) (slot : S2W_ExtractionBoundary.Slot) (initial final : A)
    (post : Heap (Nat → S2W_D189Entry.Record))
    (faithful : JHf_ValidationRefutation.Faithful (sdk (JHf_ReconstructionConfiguration.value c err))
      CPH_Program.verifier (JHb_World.e2.second secondSizes)) :
    second (JHf_NativeRefutation.native c err) allocator JHb_World.e2
      CPH_Program.verifier JHb_DataRequest.value slot initial≠ok (.Ok (post,final)) := by
  intro accepted
  exact JHf_NativeRefutation.source c err slot faithful
    (S2W_D189Wrappers.second_accepted _ allocator JHb_World.e2 _ _ slot initial final post accepted).1
#print axioms not_accepted2
end AspisR1.JHf_TX2
end

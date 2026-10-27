import SCE_Nonvacuity
import SCE_RuntimeReturn
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_ObservedFixture
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment F3T_Experiment F3T_ByteCarrier SCE_FixtureData

/-- The shared observer returns the ACTUAL submitted JFx bytes in every H.
Its source acceptance flag is left as computed. This is not an assertion of
crypto acceptance by the local CPH native witnesses. -/
theorem returned {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (H : Bytes → State) :
    ∃ run : RunView,
      (eval H (runtime c hashv copy allocator id
        (SCE_FixtureSubmission.adversary data1 data2 slot))).2 = some run ∧
      run.2.1.stored = MultiproofConeCanonical.bytesOf JFx_NativeBytes.proofBytes ∧
      run.2.1.physical.bytes = MultiproofConeCanonical.bytesOf JFx_NativeBytes.publicBytes := by
  obtain ⟨run,observed,stored,publicBytes⟩ := SCE_RuntimeReturn.returned c hashv copy allocator id
    (SCE_FixtureSubmission.adversary data1 data2 slot) H
  have actual := SCE_FixtureSubmission.original_submission data1 data2 slot H
  exact ⟨run,observed,
    stored.trans (congrArg Port1_StoredCarrier.Submission.stored actual),
    publicBytes.trans (congrArg Port1_StoredCarrier.Submission.publicBytes actual)⟩

#print axioms returned
end AspisR1.SCE_ObservedFixture
end

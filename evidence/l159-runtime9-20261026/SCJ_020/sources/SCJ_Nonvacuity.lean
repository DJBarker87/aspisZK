import SCI_FinalAudit
import SCJ_Checkpoint
import SCJ_Projection
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCJ_Nonvacuity
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
/-- Same retained real-byte fixture, not joint satisfiability of extraction
and every installed release premise. Native fixture functions are local. -/
theorem real_bytes (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (H : Bytes → State) :
    (eval H (SCE_Experiment.submission
      (SCE_FixtureSubmission.adversary data1 data2 slot))).2 =
      (⟨MultiproofConeCanonical.bytesOf JFx_NativeBytes.publicBytes,
        MultiproofConeCanonical.bytesOf JFx_NativeBytes.proofBytes⟩ : F3T_ByteCarrier.Submission) ∧
    MultiproofConeCanonical.bytesOf
      ((eval H ((SCE_FixtureSubmission.adversary data1 data2 slot).second
        (SCE_FixtureSubmission.firstInput data1) SCE_FixtureData.saved
        SCE_FixtureWrappers.post1 ())).2.entry.buffers
        ((eval H ((SCE_FixtureSubmission.adversary data1 data2 slot).second
          (SCE_FixtureSubmission.firstInput data1) SCE_FixtureData.saved
          SCE_FixtureWrappers.post1 ())).2.entry.handles 6).1).val =
      MultiproofConeCanonical.bytesOf SCE_FixtureData.saved.val :=
  SCI_FinalAudit.real_byte_fixture data1 data2 slot H

#print axioms real_bytes
#print axioms AspisR1.SCG_Nonvacuity.joint
end AspisR1.SCJ_Nonvacuity
end

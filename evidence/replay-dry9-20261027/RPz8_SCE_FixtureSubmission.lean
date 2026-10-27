import RPz8_SCE_FixtureData
import RPz8_SCE_Experiment
import RPz8_SCE_SubmissionExt
import RPz8_SCE_ByteSuffix
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_FixtureSubmission
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open GExq_AccountExperiment SCE_Experiment F3T_ByteCarrier SCE_FixtureData

theorem buffer0 : e1.buffers (e1.handles 0).1 = proofAccount := rfl
theorem buffer1 : e1.buffers (e1.handles 1).1 = JFx_NativeBytes.publicInput := rfl

def firstInput (data : Slice U8) : FirstInputs Unit := ⟨e1,data,()⟩
def secondInput (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) : SecondInputs Unit :=
  ⟨e2,data,slot,()⟩
def adversary (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) : Adversary Unit :=
  ⟨.done (firstInput data1),fun _ _ _ _ => .done (secondInput data2 slot)⟩

theorem submitted_real (data : Slice U8) :
    submitted (firstInput data) =
      (⟨MultiproofConeCanonical.bytesOf JFx_NativeBytes.publicBytes,
        MultiproofConeCanonical.bytesOf JFx_NativeBytes.proofBytes⟩ : Submission) := by
  unfold submitted firstInput
  rw [buffer0,buffer1]
  apply SCE_SubmissionExt.equal
  · rfl
  · simpa only [proofAccount] using
      SCE_ByteSuffix.replicate_prefix 688 (0#u8) JFx_NativeBytes.proofBytes


theorem original_submission (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (H : Bytes → State) :
    (eval H (submission (adversary data1 data2 slot))).2 =
      (⟨MultiproofConeCanonical.bytesOf JFx_NativeBytes.publicBytes,
        MultiproofConeCanonical.bytesOf JFx_NativeBytes.proofBytes⟩ : Submission) := by
  rw [submission_eval]
  exact submitted_real data1

#print axioms buffer0
#print axioms buffer1
#print axioms submitted_real
#print axioms original_submission
end AspisR1.SCE_FixtureSubmission
end

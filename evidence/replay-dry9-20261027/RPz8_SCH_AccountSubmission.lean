import RPz8_SCH_AccountCuts
import RPz8_SCE_FirstCutBytes
import RPz8_SCE_SubmissionExt
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCH_AccountSubmission
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation

/-- The recovered source TX1 inputs ARE the original adversary submission,
including the physical public carrier and the exact 57607-byte proof suffix. -/
theorem accepted {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A) :
    ∀ H : Bytes → State,
    SCE_Experiment.accepted (eval H (account c hashv copy allocator id a)).2 = true →
    ∃ saved post final f s,
      SourceCuts (SCH_IdealSdk.dictionary c hashv H) (eval H a.first).2.entry.first
        ((eval H (a.second (eval H a.first).2 saved post final)).2.entry.second secondSizes)
        saved f s ∧
      (eval H (submission a)).2 =
        (⟨MultiproofConeCanonical.bytesOf f.pub.val,MultiproofConeCanonical.bytesOf f.proof.val⟩ : F3T_ByteCarrier.Submission) := by
  intro H success
  obtain ⟨saved,post,final,f,s,cuts⟩ := SCH_AccountCuts.accepted c hashv copy allocator id a H success
  have bytes := SCE_FirstCutBytes.submitted_cut (eval H a.first).2 _ _ saved f s cuts
  refine ⟨saved,post,final,f,s,cuts,?_⟩
  rw [submission_eval]
  exact SCE_SubmissionExt.equal _ _ bytes.1 bytes.2

#print axioms accepted
end AspisR1.SCH_AccountSubmission
end

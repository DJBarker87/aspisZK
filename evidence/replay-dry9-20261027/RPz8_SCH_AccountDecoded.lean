import RPz8_SCH_DecodedCuts
import RPz8_SCH_AccountSubmission
import RPz8_SCH_DecodeAlign
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCH_AccountDecoded
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation

theorem accepted {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (err : C) (reservation : NP6_StdModel.Reservation)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A) :
    let r := Rc5_Install.configuration err c reservation
    ∀ H : Bytes → State,
    SCE_Experiment.accepted (eval H (account r hashv copy allocator id a)).2 = true →
    ∃ saved post final f s,
      SourceCuts (SCH_IdealSdk.dictionary r hashv H) (eval H a.first).2.entry.first
        ((eval H (a.second (eval H a.first).2 saved post final)).2.entry.second secondSizes) saved f s ∧
      Port1_Driver.decodeSemantic (DrvC_Installation.sdk r) f.pub = ok (some f.semantic) ∧
      (eval H (submission a)).2 =
        (⟨MultiproofConeCanonical.bytesOf f.pub.val,MultiproofConeCanonical.bytesOf f.proof.val⟩ : F3T_ByteCarrier.Submission) := by
  dsimp only
  intro H success
  obtain ⟨saved,post,final,one,two⟩ := SCH_AcceptedSources.accepted _ hashv copy allocator id a H success
  obtain ⟨f,s,cuts,decoded⟩ := SCH_DecodedCuts.pair _ id _ _ _ _ _ saved one two
  rw [SCH_DecodeAlign.installed c err reservation hashv H] at decoded
  have bytes := SCE_FirstCutBytes.submitted_cut (eval H a.first).2 _ _ saved f s cuts
  refine ⟨saved,post,final,f,s,cuts,decoded,?_⟩
  rw [submission_eval]
  exact SCE_SubmissionExt.equal _ _ bytes.1 bytes.2

#print axioms accepted
end AspisR1.SCH_AccountDecoded
end

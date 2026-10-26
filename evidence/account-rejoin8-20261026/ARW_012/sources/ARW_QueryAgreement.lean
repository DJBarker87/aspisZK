import ARW_WrapperNative
import ART_AdversaryWork
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARW_QueryAgreement
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment
theorem exact {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish c.reserved
        c.query c.geometry c.boundaries c.std) native1 native2 hashv)
    (a : Adversary A) (H : Bytes → State)
    (agrees : ARS_QueryTransport.Agrees H (SdkC_Source.run hashv
      (ARS_NativeAccount.firstSyntax c hashv copy allocator id (eval H a.first).2) []).2) :
    (ARW_Induced.issued native1 copy allocator id a H).length =
      ART_AdversaryWork.work c hashv copy allocator id a H := by
  have same := ARW_WrapperNative.first c hashv copy allocator id native1 native2 extraction (eval H a.first).2 H agrees
  simp only [ARW_Induced.issued,ART_AdversaryWork.work,same,List.length_append]
  cases reply : S2W_D189Wrappers.first native1 copy allocator (eval H a.first).2.entry id
      (eval H a.first).2.data (eval H a.first).2.state with
  | fail error => rfl
  | div => rfl
  | ok result =>
    cases result with
    | Err error => rfl
    | Ok value =>
      rcases value with ⟨saved,post,final⟩
      rfl

#print axioms exact
end AspisR1.ARW_QueryAgreement
end

import ARV_PaddingChoice
import ART_AdversaryWork
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_PaddingWork
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment GExq_AccountExperiment

theorem exact {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (address : Bytes) (count : Nat) (H : Bytes → State)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (yes : (eval H (ART_PartialAccount.wrapper hashv
      (ARS_NativeAccount.firstSyntax c hashv copy allocator id (eval H a.first).2))).2 =
      ok (.Ok (saved,post,final))) :
    ART_AdversaryWork.work c hashv copy allocator id (ARQ_ChoiceCoverage.pad a address count) H =
      ART_AdversaryWork.work c hashv copy allocator id a H + count := by
  simp only [ART_AdversaryWork.work,ARQ_ChoiceCoverage.first,yes,ARQ_ChoiceCoverage.choice_length,Nat.add_assoc]

#print axioms exact
end AspisR1.ARV_PaddingWork
end

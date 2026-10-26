import ART_AccountAccepted
import ART_Runtime
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_RuntimeAccepted
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment

theorem exact {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (H : Bytes → State)
    (accepted : SCE_Experiment.accepted
      (eval H (ART_PartialAccount.account c hashv copy allocator id a)).2 = true) :
    eval H (ART_Runtime.runtime c hashv copy allocator id a) =
      eval H (SCE_Experiment.runtime c hashv copy allocator id a) := by
  rw [ART_Runtime.eval_runtime,SCE_Experiment.runtime_eval,
    ART_AccountAccepted.exact c hashv copy allocator id a H accepted]

#print axioms exact
end AspisR1.ART_RuntimeAccepted
end

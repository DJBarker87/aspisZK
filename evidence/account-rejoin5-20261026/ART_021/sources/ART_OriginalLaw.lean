import ART_Cost
import ART_Outcome
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_OriginalLaw
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open GExq_AccountExperiment SCE_Experiment ARS_NativeAccount ART_PartialAccount

theorem exact {A F C V : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (native H : Bytes → State)
    (certificate : ART_PartialAccount.Certificate c hashv copy allocator id a native H)
    (observe : Outcome A → Nat → V) :
    observe (eval H (ART_PartialAccount.account c hashv copy allocator id a)).2
      (eval H (ART_PartialAccount.account c hashv copy allocator id a)).1.length =
    observe (ARS_NativeAccount.run c hashv copy allocator id a native).2
      (attempts c hashv copy allocator id a native) := by
  rw [ART_Outcome.exact c hashv copy allocator id a native H certificate,
    ART_Cost.exact c hashv copy allocator id a native H certificate]

#print axioms exact
end AspisR1.ART_OriginalLaw
end

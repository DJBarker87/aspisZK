import ART_QueriedCoverage
import ART_Runtime
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_QueriedRuntime
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment

theorem exact {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (native H : Bytes → State)
    (consistent : ARS_AccountReplay.Consistent
      (ART_PartialAccount.account c hashv copy allocator id a) native H) :
    eval H (ART_Runtime.runtime c hashv copy allocator id a) =
      eval native (ART_Runtime.runtime c hashv copy allocator id a) := by
  rw [ART_Runtime.eval_runtime,ART_Runtime.eval_runtime,ARS_AccountReplay.replay _ native H consistent]

#print axioms exact
end AspisR1.ART_QueriedRuntime
end

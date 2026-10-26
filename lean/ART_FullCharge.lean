import ART_FullBudget
import ARQ_Observer
import RPx_ChargeBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_FullCharge
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem charged {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : SCE_Experiment.Adversary A)
    (Q : Nat) (bound : ART_AdversaryWork.Bound c hashv copy allocator id a Q) :
    (∀ H, FS.firstReads FS.emptyTable (eval H (Hiq_RecordedJoint.program
      (ART_PartialAccount.account c hashv copy allocator id a) ARQ_Observer.project
      (ARQ_Observer.select c id))).1 ≤ Q+2965) ∧
    F3T_AccountCharge.mass (ART_PartialAccount.account c hashv copy allocator id a)
      ARQ_Observer.project (ARQ_Observer.select c id) Q ≤ F3T_Numeric.accountLoss Q :=
  RPx_ChargeBudget.charge _ Q (ART_FullBudget.issued c hashv copy allocator id a Q bound)
    ARQ_Observer.project (ARQ_Observer.select c id)

#print axioms charged
end AspisR1.ART_FullCharge
end

import ARQ_Observer
import SCF_Charge
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_AccountCharge
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment

/-- The actual deterministic checkpoint-query and physical-byte selectors
use the unchanged accountLoss. This is a charge result, not failure domination. -/
theorem charged {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H a.first).1.length ≤ Q0)
    (choiceBound : ∀ i saved post final H, (eval H (a.second i saved post final)).1.length ≤ Q1) :
    (∀ H, (eval H (account c hashv copy allocator id a)).1.length ≤ Q0+Q1+1921) ∧
    (∀ H, FS.firstReads FS.emptyTable
      (eval H (Hiq_RecordedJoint.program (account c hashv copy allocator id a)
        ARQ_Observer.project (ARQ_Observer.select c id))).1 ≤ Q0+Q1+2965) ∧
    F3T_AccountCharge.mass (account c hashv copy allocator id a)
      ARQ_Observer.project (ARQ_Observer.select c id) (Q0+Q1) ≤ F3T_Numeric.accountLoss (Q0+Q1) :=
  SCF_Charge.charged c hashv copy allocator id a Q0 Q1 prefixBound choiceBound
    ARQ_Observer.project (ARQ_Observer.select c id)

#print axioms charged
end AspisR1.ARQ_AccountCharge
end

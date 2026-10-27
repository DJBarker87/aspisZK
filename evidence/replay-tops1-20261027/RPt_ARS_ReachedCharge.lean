import RPt_ARS_ReachedBudget
import RPz8_ARQ_Observer
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARS_ReachedCharge
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment

/-- Original full account charge with only an actually reached adaptive budget.
The selector and event remain ARQ's exact Q0+Q1+2965 account event. -/
theorem charged {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (Q0 Q1 : Nat) (prefixBound : ∀ H, (eval H a.first).1.length ≤ Q0)
    (choiceBound : ARS_ReachedBudget.ChoiceBound c hashv copy allocator id a Q1) :
    (∀ H, (eval H (account c hashv copy allocator id a)).1.length ≤ Q0+Q1+1921) ∧
    (∀ H, FS.firstReads FS.emptyTable
      (eval H (Hiq_RecordedJoint.program (account c hashv copy allocator id a)
        ARQ_Observer.project (ARQ_Observer.select c id))).1 ≤ Q0+Q1+2965) ∧
    F3T_AccountCharge.mass (account c hashv copy allocator id a)
      ARQ_Observer.project (ARQ_Observer.select c id) (Q0+Q1) ≤ F3T_Numeric.accountLoss (Q0+Q1) := by
  have budget := ARS_ReachedBudget.issued c hashv copy allocator id a Q0 Q1 prefixBound choiceBound
  exact ⟨budget,RPx_ChargeBudget.charge _ (Q0+Q1) budget ARQ_Observer.project (ARQ_Observer.select c id)⟩

#print axioms charged
end AspisR1.ARS_ReachedCharge
end

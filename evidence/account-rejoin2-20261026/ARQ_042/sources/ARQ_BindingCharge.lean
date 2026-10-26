import ARQ_AccountCharge
import P2P_Charge
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_BindingCharge
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment

/-- Physical proof/public byte binding is available or charged on exactly
this observer. The account event and its mass are the SAME instance. -/
theorem alternative {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H a.first).1.length ≤ Q0)
    (choiceBound : ∀ i saved post final H, (eval H (a.second i saved post final)).1.length ≤ Q1)
    (H : Bytes → State) :
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
      (eval H (Hiq_RecordedJoint.program (account c hashv copy allocator id a)
        ARQ_Observer.project (ARQ_Observer.select c id))) ∨
    R9PoolRuntimeBinding.P2Prime H
      (ARQ_Observer.select c id (eval H (account c hashv copy allocator id a)).2).1
      (ARQ_Observer.select c id (eval H (account c hashv copy allocator id a)).2).2 := by
  apply P2P_Charge.binding_or_collision _ _ _ (Q0+Q1) _ H
  intro h
  exact (VerifierCallBudget.firstReads_le_length _ _).trans
    ((ARQ_AccountCharge.charged c hashv copy allocator id a Q0 Q1 prefixBound choiceBound).1 h)

#print axioms alternative
end AspisR1.ARQ_BindingCharge
end

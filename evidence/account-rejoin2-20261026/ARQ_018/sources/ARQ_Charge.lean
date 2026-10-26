import ARQ_Observer
import SCF_Charge
import F3X_CollisionErase
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_Charge
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment

/-- Charge the canonical local alternative on THIS complete account. The
terminal preparation must already have been read; no interior read is erased.
These two explicit preparation premises are local instantiation obligations,
not new trust assumptions and not a proof of ARQ_Join.Target. -/
theorem cached_preparation {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H a.first).1.length ≤ Q0)
    (choiceBound : ∀ i saved post final H, (eval H (a.second i saved post final)).1.length ≤ Q1)
    (preparation : Program Bytes State Unit) (H : Bytes → State)
    (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (projected : ARQ_Observer.project (eval H (account c hashv copy allocator id a)).2 = (p,q))
    (included : ∀ addr, FS2.Duplex.Read (eval H preparation).1 addr →
      FS2.Duplex.Read (eval H (account c hashv copy allocator id a)).1 addr)
    (collision : AuS1_Finish.Collision H
      ((eval H (account c hashv copy allocator id a)).1 ++ (eval H preparation).1) p q) :
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
      (eval H (Hiq_RecordedJoint.program (account c hashv copy allocator id a)
        ARQ_Observer.project (ARQ_Observer.select c id))) := by
  have issued := (SCF_Charge.charged c hashv copy allocator id a Q0 Q1 prefixBound choiceBound
    ARQ_Observer.project (ARQ_Observer.select c id)).1
  have budget : ∀ H, FS.firstReads FS.emptyTable
      (eval H (account c hashv copy allocator id a)).1 ≤ Q0+Q1+1921 := by
    intro h
    exact (VerifierCallBudget.firstReads_le_length _ _).trans (issued h)
  apply F3U_AccountEvent.charged (account c hashv copy allocator id a)
    ARQ_Observer.project (ARQ_Observer.select c id) (Q0+Q1) budget H
  rw [projected]
  exact (F3X_CollisionErase.same H _ _ p q
    (Op5I_AcceptedCarrierCounterexample.evaluated_reply H _)
    (Op5I_AcceptedCarrierCounterexample.evaluated_reply H preparation) included).mp collision

#print axioms cached_preparation
end AspisR1.ARQ_Charge
end

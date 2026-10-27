import RPz8_ARQ_Observer
import RPz8_ART_FullBudget
import RPz8_ARX_LocalCharge
import RPz8_SCF_Charge
import RPz8_F3X_CollisionErase
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARX_CachedCharge
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
    (a : Adversary A) (Q : Nat)
    (H : Bytes → State)
    (bound : ART_AdversaryWork.work c hashv copy allocator id a H ≤ Q)
    (preparation : Program Bytes State Unit)
    (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (projected : ARQ_Observer.project (eval H (ART_PartialAccount.account c hashv copy allocator id a)).2 = (p,q))
    (included : ∀ addr, FS2.Duplex.Read (eval H preparation).1 addr →
      FS2.Duplex.Read (eval H (ART_PartialAccount.account c hashv copy allocator id a)).1 addr)
    (collision : AuS1_Finish.Collision H
      ((eval H (ART_PartialAccount.account c hashv copy allocator id a)).1 ++ (eval H preparation).1) p q) :
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
      (eval H (Hiq_RecordedJoint.program (ART_PartialAccount.account c hashv copy allocator id a)
        ARQ_Observer.project (ARQ_Observer.select c id))) := by
  apply ARX_LocalCharge.canonical (ART_PartialAccount.account c hashv copy allocator id a)
    ARQ_Observer.project (ARQ_Observer.select c id) Q H
    (ARW_LocalBudget.issued c hashv copy allocator id a Q H bound)
  rw [projected]
  exact (F3X_CollisionErase.same H _ _ p q
    (Op5I_AcceptedCarrierCounterexample.evaluated_reply H _)
    (Op5I_AcceptedCarrierCounterexample.evaluated_reply H preparation) included).mp collision

#print axioms cached_preparation
end AspisR1.ARX_CachedCharge
end

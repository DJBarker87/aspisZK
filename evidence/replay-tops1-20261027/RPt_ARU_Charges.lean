import RPt_ART_FullCharge
import RPt_ART_StartCharge
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_Charges
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment F3T_ByteCarrier

/-- Full adaptive work, rejected prefixes, and the one-transcript Q+34 starts
on the same adversary. No second transcript or new failure event is introduced. -/
theorem charged {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (D : LiteralByteProtocol.Decoder) (Q : Nat)
    (bound : ART_AdversaryWork.Bound c hashv copy allocator id a Q) :
    (∀ H, FS.firstReads FS.emptyTable (eval H (Hiq_RecordedJoint.program
      (ART_PartialAccount.account c hashv copy allocator id a) ARQ_Observer.project
      (ARQ_Observer.select c id))).1 ≤ Q+2965) ∧
    F3T_AccountCharge.mass (ART_PartialAccount.account c hashv copy allocator id a)
      ARQ_Observer.project (ARQ_Observer.select c id) Q ≤ F3T_Numeric.accountLoss Q ∧
    (∀ H, DecodedFirstReadUnionBound.decoderFirstReads RecordedBinaryExperimentBin.dec FS.emptyTable
      (eval H (F3T_Charged.charged D (F3T_Canon.canon (lift c (submission a))))).1 ≤ Q+34) := by
  have account := ART_FullCharge.charged c hashv copy allocator id a Q bound
  exact ⟨account.1,account.2,ART_StartCharge.first_starts c D a Q
    (ART_AdversaryWork.first c hashv copy allocator id a Q bound)⟩

#print axioms charged
end AspisR1.ARU_Charges
end

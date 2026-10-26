import ART_FullBudget
import ART_StartCharge
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_StartFromWork
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem starts {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : SCE_Experiment.Adversary A)
    (Q : Nat) (bound : ART_AdversaryWork.Bound c hashv copy allocator id a Q)
    (D : LiteralByteProtocol.Decoder) (H : Bytes → State) :
    DecodedFirstReadUnionBound.decoderFirstReads RecordedBinaryExperimentBin.dec FS.emptyTable
      (eval H (F3T_Charged.charged D (F3T_Canon.canon (F3T_ByteCarrier.lift c (SCE_Experiment.submission a))))).1 ≤ Q+34 :=
  ART_StartCharge.first_starts c D a Q (ART_AdversaryWork.first c hashv copy allocator id a Q bound) H

#print axioms starts
end AspisR1.ART_StartFromWork
end

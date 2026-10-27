import ARV_Filter
import ART_FullBudget
import ARU_Charges
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_FilterCharge
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment
attribute [local instance] Classical.propDecidable

variable {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A)

theorem issued (Q : Nat)
    (bound : ART_AdversaryWork.Bound (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a Q)
    (H : Bytes → State) :
    (eval H (ARV_Filter.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a)).1.length ≤ Q+1921 := by
  rw [ARV_Filter.query_log]
  exact ART_FullBudget.issued (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a Q bound H

theorem starts (D : LiteralByteProtocol.Decoder) (Q : Nat)
    (bound : ART_AdversaryWork.Bound (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a Q) :
    ∀ H, DecodedFirstReadUnionBound.decoderFirstReads RecordedBinaryExperimentBin.dec FS.emptyTable
      (eval H (F3T_Charged.charged D (F3T_Canon.canon
        (F3T_ByteCarrier.lift (FIp_Install.configuration err c r) (submission a))))).1 ≤ Q+34 :=
  (ARU_Charges.charged (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a D Q bound).2.2

#print axioms issued
#print axioms starts
end AspisR1.ARV_FilterCharge
end

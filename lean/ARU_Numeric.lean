import ARU_Mass
import F3T_Combined
import F3T_RuntimeBound
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_Numeric
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation
theorem conditional {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A)
    (std : S2W_TrustedStd.TrustedStd copy) (D : LiteralByteProtocol.Decoder)
    (words : CanonicalCutEnrichedTranscript.Words)
    (owners : FIp_GlobalOwners.Owners (FIp_Install.configuration err c r)
      (Rc2_Install.configuration (Rc5_Install.seed err (FIp_Install.select r c)) r).boundaries)
    (Q : Nat) (bound : ART_AdversaryWork.Bound (FIp_Install.configuration err c r)
      hashv copy allocator CPH_Program.verifier a Q) 
    (support : ARU_AllWorld.Supported (Tx := Tx) L copy allocator c err r native1 native2 hashv a) :
    F3T_RuntimeBound.failureModel (ART_Runtime.runtime (FIp_Install.configuration err c r)
      hashv copy allocator CPH_Program.verifier a) ≤ F3T_Numeric.total Q := by
  let cfg := FIp_Install.configuration err c r
  have mass := ARU_Mass.conditional L copy allocator c err r native1 native2 hashv extraction a std D words owners Q bound support
  have lifted : ∀ H : Bytes → State, (eval H (F3T_ByteCarrier.lift cfg (submission a))).1.length ≤ Q := by
    intro H
    rw [F3T_ByteCarrier.lift_eval,submission_eval]
    exact ART_AdversaryWork.first cfg hashv copy allocator CPH_Program.verifier a Q bound H
  have model := add_le_add (F3T_ModelClaims.failure_bound D (F3T_ByteCarrier.lift cfg (submission a)) Q lifted)
    (le_refl (F3T_Numeric.accountLoss Q))
  rw [F3T_Combined.arithmetic] at model
  unfold F3T_RuntimeBound.failureModel F3T_ModelClaims.failure at *
  linarith

#print axioms conditional
end AspisR1.ARU_Numeric
end

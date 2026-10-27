import RPt_FJp_Mass
import RPz8_ARX_SubmissionBudget
import RPz8_F3U_Range
import RPz8_F3U_Numeric
import RPz7_F3T_Combined
import RPz7_F3T_RuntimeBound
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJp_Residual
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation
theorem numeric {W A C Tx : Type} (L : Library W (Nat → Record))
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
    (owners : FJp_GlobalOwners.Owners (FIp_Install.configuration err c r)
      (Rc2_Install.configuration (Rc5_Install.seed err (FIp_Install.select r c)) r).boundaries)
    (Q0 Q1 : Nat)
    (queries : ∀ H, (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a H).length ≤ Q0+Q1) :
    F3T_RuntimeBound.failureModel (ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a) ≤ F3T_Numeric.total (Q0+Q1) := by
  let cfg := FIp_Install.configuration err c r
  have mass := FJp_Mass.bounded (Tx := Tx) L copy allocator c err r native1 native2 hashv a extraction std D words owners Q0 Q1 queries
  have lifted : ∀ H : Bytes → State, (eval H (F3T_ByteCarrier.lift cfg (submission a))).1.length ≤ Q0+Q1 := by
    intro H
    rw [F3T_ByteCarrier.lift_eval]
    exact ARX_SubmissionBudget.bound native1 copy allocator CPH_Program.verifier a (Q0+Q1) queries H
  have model := add_le_add (F3T_ModelClaims.failure_bound D (F3T_ByteCarrier.lift cfg (submission a)) (Q0+Q1) lifted)
    (le_refl (F3T_Numeric.accountLoss (Q0+Q1)))
  rw [F3T_Combined.arithmetic] at model
  unfold F3T_RuntimeBound.failureModel F3T_ModelClaims.failure at *
  linarith

/-- The same exact zero-query margin as the approved frozen3 model. -/
theorem margin_exact :
    1/(2:Rat)^100-F3T_Numeric.total 0 =
      1/(2:Rat)^108 - 6*((1161:Rat)^2+2965^2)/(2:Rat)^256 -
      1/(2:Rat)^126 - 1/(2:Rat)^454 := F3T_Numeric.margin_exact

#print axioms numeric
#print axioms margin_exact
end AspisR1.FJp_Residual
end

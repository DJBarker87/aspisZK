import ARV_FilterNumeric
import F3U_Range
import F3U_Numeric
import F3T_Combined
import F3T_RuntimeBound
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_FilterRange
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation
theorem bounded {W A C Tx : Type} (L : Library W (Nat → Record))
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
    :
    (Q ≤ F3U_RangeEdges.maxQueries →
      F3T_RuntimeBound.failureModel (ARV_Filter.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a) ≤ (Q+1:Rat)*(1/(2:Rat)^100)) ∧
    (Q = 0 → F3U_Numeric.margin ≤ 1/(2:Rat)^100-
      F3T_RuntimeBound.failureModel (ARV_Filter.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a) ∧
      F3T_RuntimeBound.failureModel (ARV_Filter.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a) < 1/(2:Rat)^100) := by
  have bounded := ARV_FilterNumeric.bounded (Tx := Tx) L copy allocator c err r native1 native2 hashv extraction a std D words owners Q bound
  constructor
  · intro range
    exact bounded.trans (F3U_Range.per_attempt Q range)
  · intro zero
    rw [zero] at bounded
    exact F3U_Numeric.runtime_margin _ bounded

#print axioms bounded
end AspisR1.ARV_FilterRange
end

import ARV_FilterRange
import ARV_FilterCharge
import ARV_FilterPerCoin
import ARV_FilterCheckpoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_FilterTop
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation
/-- Bound for the explicit noncomputable support-filtered mathematical
observer only. This is NOT ARV_Root.deployed or a deployed-law equivalence. -/
theorem proposed {W A C Tx : Type} (L : Library W (Nat → Record))
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
    F3T_RuntimeBound.failureModel (ARV_Filter.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a) ≤ F3T_Numeric.total Q ∧
    (Q ≤ F3U_RangeEdges.maxQueries →
      F3T_RuntimeBound.failureModel (ARV_Filter.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a) ≤
        (Q+1:Rat)*(1/(2:Rat)^100)) ∧
    (Q = 0 → F3U_Numeric.margin ≤ 1/(2:Rat)^100-
      F3T_RuntimeBound.failureModel (ARV_Filter.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a) ∧
      F3T_RuntimeBound.failureModel (ARV_Filter.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a) < 1/(2:Rat)^100) ∧
    (∀ H, (eval H (ARV_Filter.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a)).1.length ≤ Q+1921) ∧
    (∀ H, DecodedFirstReadUnionBound.decoderFirstReads RecordedBinaryExperimentBin.dec FS.emptyTable
      (eval H (F3T_Charged.charged D (F3T_Canon.canon
        (F3T_ByteCarrier.lift (FIp_Install.configuration err c r) (submission a))))).1 ≤ Q+34) := by
  have range := ARV_FilterRange.bounded (Tx := Tx) L copy allocator c err r native1 native2 hashv extraction a std D words owners Q bound
  exact ⟨ARV_FilterNumeric.bounded (Tx := Tx) L copy allocator c err r native1 native2 hashv extraction a std D words owners Q bound,
    range.1,range.2,ARV_FilterCharge.issued (Tx := Tx) L copy allocator c err r native1 native2 hashv a Q bound,
    ARV_FilterCharge.starts copy allocator c err r hashv a D Q bound⟩

#print axioms proposed
end AspisR1.ARV_FilterTop
end

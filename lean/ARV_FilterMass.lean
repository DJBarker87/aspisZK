import ARV_FilterDomination
import ARU_RuntimeMass
import ART_FullCharge
import F3U_Averaging
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_FilterMass
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound

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
    F3T_Runtime.deployedFailure (ARV_Filter.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a) ≤
      lazyMean (F3T_Charged.projected D (F3T_Canon.canon
        (F3T_ByteCarrier.lift (FIp_Install.configuration err c r) (submission a)))) FS.emptyTable
        RawRecordedOracleExtractionMassBin.failureMass + F3T_Numeric.accountLoss Q := by
  let cfg := FIp_Install.configuration err c r
  have pointwise : ∀ H,
      F3T_Runtime.runtimeMass (eval H (ARV_Filter.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a)) ≤
        RawRecordedOracleExtractionMassBin.failureMass
          (eval H (F3T_Charged.projected D (F3T_Canon.canon (F3T_ByteCarrier.lift cfg (submission a))))) +
          indicator (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
            (eval H (Hiq_RecordedJoint.program (ART_PartialAccount.account cfg hashv copy allocator CPH_Program.verifier a)
              ARQ_Observer.project (ARQ_Observer.select cfg CPH_Program.verifier)))) := by
    intro H
    exact ARV_FilterDomination.pointwise L copy allocator c err r native1 native2 hashv extraction a H std D words owners Q bound
  have averaged := F3U_Averaging.charge (ARV_Filter.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a)
    (F3T_Charged.projected D (F3T_Canon.canon (F3T_ByteCarrier.lift cfg (submission a))))
    (Hiq_RecordedJoint.program (ART_PartialAccount.account cfg hashv copy allocator CPH_Program.verifier a)
      ARQ_Observer.project (ARQ_Observer.select cfg CPH_Program.verifier))
    F3T_Runtime.runtimeMass RawRecordedOracleExtractionMassBin.failureMass
    (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)) pointwise
  change F3T_Runtime.deployedFailure (ARV_Filter.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a) ≤
    lazyMean (F3T_Charged.projected D (F3T_Canon.canon (F3T_ByteCarrier.lift cfg (submission a)))) FS.emptyTable
      RawRecordedOracleExtractionMassBin.failureMass +
    F3T_AccountCharge.mass (ART_PartialAccount.account cfg hashv copy allocator CPH_Program.verifier a)
      ARQ_Observer.project (ARQ_Observer.select cfg CPH_Program.verifier) Q at averaged
  exact averaged.trans (add_le_add (le_refl _) (ART_FullCharge.charged cfg hashv copy allocator CPH_Program.verifier a Q bound).2)

#print axioms bounded
end AspisR1.ARV_FilterMass
end

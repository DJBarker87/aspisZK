import ARU_PerCoin
import ARV_FilterSupport
import ARV_FilterPhysical
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_FilterPerCoin
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation
theorem extract {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) (H : Bytes → State)
    (run : F3T_Experiment.RunView)
    (observed : (eval H (ARV_Filter.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a)).2 = some run)
    (yes : run.2.2 = true)
    (std : S2W_TrustedStd.TrustedStd copy) (D : LiteralByteProtocol.Decoder)
    (words : CanonicalCutEnrichedTranscript.Words)
    (owners : FIp_GlobalOwners.Owners (FIp_Install.configuration err c r)
      (Rc2_Install.configuration (Rc5_Install.seed err (FIp_Install.select r c)) r).boundaries)
    (Q : Nat) (bound : ART_AdversaryWork.Bound (FIp_Install.configuration err c r)
      hashv copy allocator CPH_Program.verifier a Q)
    (clean : ¬ BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
      (eval H (Hiq_RecordedJoint.program
        (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)
        ARQ_Observer.project (ARQ_Observer.select (FIp_Install.configuration err c r) CPH_Program.verifier)))) :
    ∀ coins : GSConcreteByteDecoderBank.RawCoins,
      RawRecordedPublicSpendExtractorBin.extract (F3T_Experiment.view run) coins =
        RawRecordedPublicSpendExtractorBin.extract (eval H (F3T_Charged.projected D (F3T_Canon.canon (F3T_ByteCarrier.lift (FIp_Install.configuration err c r) (submission a))))) coins := by
  obtain ⟨n⟩ := ARV_FilterSupport.accepted L copy allocator c err r native1 native2 hashv a extraction H run observed yes
  rw [ARV_FilterPhysical.observed L copy allocator c err r native1 native2 hashv a H run observed]
  exact ARU_PerCoin.extract L copy allocator c err r native1 native2 hashv extraction a H n std D words owners Q bound clean

#print axioms extract
end AspisR1.ARV_FilterPerCoin
end

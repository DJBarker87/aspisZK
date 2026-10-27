import RPz8_ARX_Domination
import RPz8_ARX_AdmittedRuntime
import RPz8_ARW_AdmittedBudget
import RPz8_ARU_RuntimeMass
import RPz8_ARX_LocalCharge
import RPz8_F3U_Averaging
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARX_Mass
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment
attribute [local instance] Classical.propDecidable

variable {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A)


theorem bounded
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (std : S2W_TrustedStd.TrustedStd copy) (D : LiteralByteProtocol.Decoder)
    (words : CanonicalCutEnrichedTranscript.Words)
    (owners : FIp_GlobalOwners.Owners (FIp_Install.configuration err c r)
      (Rc2_Install.configuration (Rc5_Install.seed err (FIp_Install.select r c)) r).boundaries)
    (Q0 Q1 : Nat)
    (queries : ∀ H, (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a H).length ≤ Q0+Q1) :
    F3T_Runtime.deployedFailure (ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a) ≤
      lazyMean (F3T_Charged.projected D (F3T_Canon.canon
        (F3T_ByteCarrier.lift (FIp_Install.configuration err c r) (submission a)))) FS.emptyTable
        RawRecordedOracleExtractionMassBin.failureMass + F3T_Numeric.accountLoss (Q0+Q1) := by
  let cfg := FIp_Install.configuration err c r
  let source := ART_PartialAccount.account cfg hashv copy allocator CPH_Program.verifier a
  let capped := ARX_LocalCharge.bounded source (Q0+Q1)
  let model := F3T_Charged.projected D (F3T_Canon.canon (F3T_ByteCarrier.lift cfg (submission a)))
  let runtime := ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a
  let recorder := Hiq_RecordedJoint.program capped ARQ_Observer.project (ARQ_Observer.select cfg CPH_Program.verifier)
  let event : View Bytes State (View Bytes State (GExq_AccountExperiment.Outcome A)) → Prop := BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
  have each : ∀ H, F3T_Runtime.runtimeMass (eval H runtime) ≤
      RawRecordedOracleExtractionMassBin.failureMass (eval H model) +
        AspisV8R19.CausalFirstHitUnionBound.indicator (event (eval H recorder)) := by
    intro H
    by_cases supported : Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H)
    · obtain ⟨n⟩ := supported
      have budget := ARW_AdmittedBudget.issued L copy allocator c err r native1 native2 hashv extraction a H n Q0 Q1 queries
      have same := ARX_LocalCharge.exact source (Q0+Q1) H budget.2
      have dominate := ARX_Domination.pointwise L copy allocator c err r native1 native2 hashv extraction a H n
        std D words owners (Q0+Q1) budget.1
      change F3T_Runtime.runtimeMass (eval H (ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a)) ≤ _
      rw [ARX_AdmittedRuntime.on_admitted L copy allocator c err r native1 native2 hashv a extraction H n,
        ARU_RuntimeMass.pointwise]
      dsimp only [recorder,capped,event,model]
      rw [ARX_LocalCharge.congr_source _ _ ARQ_Observer.project (ARQ_Observer.select cfg CPH_Program.verifier) H same]
      exact dominate
    · have no := ARX_AdmittedRuntime.outside L copy allocator c err r native1 native2 hashv a extraction H supported
      change F3T_Runtime.runtimeMass (eval H (ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a)) ≤ _
      unfold F3T_Runtime.runtimeMass
      rw [no]
      have positive := F3T_Runtime.nonnegative (eval H model)
      unfold AspisV8R19.CausalFirstHitUnionBound.indicator
      split_ifs <;> linarith
  have average := F3U_Averaging.charge runtime model recorder F3T_Runtime.runtimeMass
    RawRecordedOracleExtractionMassBin.failureMass event each
  have charge := F3T_AccountCharge.bound capped ARQ_Observer.project (ARQ_Observer.select cfg CPH_Program.verifier) (Q0+Q1)
    (fun H => (VerifierCallBudget.firstReads_le_length _ _).trans (ARX_LocalCharge.budget source (Q0+Q1) H))
  exact average.trans (add_le_add (le_refl _) charge)

#print axioms bounded
end AspisR1.ARX_Mass
end

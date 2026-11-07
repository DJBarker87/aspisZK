import RPu_FJp_Mass
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNC_RuntimePointwise
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


theorem each
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (std : S2W_TrustedStd.TrustedStd copy) (D : LiteralByteProtocol.Decoder)
    (words : CanonicalCutEnrichedTranscript.Words)
    (owners : FJp_GlobalOwners.Owners (FIp_Install.configuration err c r)
      (Rc2_Install.configuration (Rc5_Install.seed err (FIp_Install.select r c)) r).boundaries)
    (Q0 Q1 : Nat)
    (queries : ∀ H, (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a H).length ≤ Q0+Q1) :
    let cfg := FIp_Install.configuration err c r
    let source := ART_PartialAccount.account cfg hashv copy allocator CPH_Program.verifier a
    let model := F3T_Charged.projected D (F3T_Canon.canon (F3T_ByteCarrier.lift cfg (submission a)))
    let runtime := ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a
    ∀ H, F3T_Runtime.runtimeMass (eval H runtime) ≤
      RawRecordedOracleExtractionMassBin.failureMass (eval H model) +
      AspisV8R19.CausalFirstHitUnionBound.indicator
        (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
          (eval H (Hiq_RecordedJoint.program (ARX_LocalCharge.bounded source (Q0+Q1))
            ARQ_Observer.project (ARQ_Observer.select cfg CPH_Program.verifier)))) := by
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
      have dominate := FJp_Domination.pointwise L copy allocator c err r native1 native2 hashv extraction a H n
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
  exact each

#print axioms each
end AspisR1.NNC_RuntimePointwise
end

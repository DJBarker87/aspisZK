import NNC_RuntimePointwise
import NNC_NoSecondCharge
import NNC_ActualChoices
import RPz8_ARX_SubmissionBudget
import RPz7_F3T_Combined
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNC_RecordedEnvelope
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment FS FS2
attribute [local instance] Classical.propDecidable
/- Unconditional numerical envelope: no native inclusion is assumed here.
The SAME E_rec covers both uses, by max rather than a sum of two charges.
The mean is over every H; neither Realizes nor admitted support is tested by
its event indicator. To claim the final actual-native theorem one must STILL
prove that the complete actual weak-entry assembly is covered by this envelope.
That source/occurrence installation is not supplied by arithmetic. -/
variable {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A)


theorem bound
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (std : S2W_TrustedStd.TrustedStd copy) (D : LiteralByteProtocol.Decoder)
    (words : CanonicalCutEnrichedTranscript.Words)
    (owners : FJp_GlobalOwners.Owners (FIp_Install.configuration err c r)
      (Rc2_Install.configuration (Rc5_Install.seed err (FIp_Install.select r c)) r).boundaries)
    (Q0 Q1 : Nat)
    (queries : ∀ H, (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a H).length ≤ Q0+Q1)
 :
    let cfg := FIp_Install.configuration err c r
    let runtime := ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a
    let source := ART_PartialAccount.account cfg hashv copy allocator CPH_Program.verifier a
    let recorder := Hiq_RecordedJoint.program (ARX_LocalCharge.bounded source (Q0+Q1))
      ARQ_Observer.project (ARQ_Observer.select cfg CPH_Program.verifier)
    let model := F3T_Charged.projected D (F3T_Canon.canon (F3T_ByteCarrier.lift cfg (submission a)))
    lazyMean (F3U_Joint.program runtime recorder model) emptyTable
      (fun v => max (F3T_Runtime.runtimeMass v.2.1)
        (AspisV8R19.CausalFirstHitUnionBound.indicator
          (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965) v.2.2.1))) +
      QueryScanModelFailure.failureProbability (2^18) ≤ F3T_Numeric.total (Q0+Q1) := by
  let cfg := FIp_Install.configuration err c r
  let source := ART_PartialAccount.account cfg hashv copy allocator CPH_Program.verifier a
  let capped := ARX_LocalCharge.bounded source (Q0+Q1)
  let recorder := Hiq_RecordedJoint.program capped ARQ_Observer.project (ARQ_Observer.select cfg CPH_Program.verifier)
  let runtime := ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a
  let model := F3T_Charged.projected D (F3T_Canon.canon (F3T_ByteCarrier.lift cfg (submission a)))
  let event := BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
  have each := NNC_RuntimePointwise.each (Tx := Tx) L copy allocator c err r native1 native2 hashv a
    extraction std D words owners Q0 Q1 queries
  have averaged := NNC_NoSecondCharge.average recorder runtime model F3T_Runtime.runtimeMass
    RawRecordedOracleExtractionMassBin.failureMass event capped ARQ_Observer.project
    (ARQ_Observer.select cfg CPH_Program.verifier) (Q0+Q1)
    (fun K => (VerifierCallBudget.firstReads_le_length _ _).trans (ARX_LocalCharge.budget source (Q0+Q1) K))
    (fun H => F3T_Runtime.nonnegative (eval H model)) each (fun _ h => h)
  have lifted : ∀ H : Bytes → State, (eval H (F3T_ByteCarrier.lift cfg (submission a))).1.length ≤ Q0+Q1 := by
    intro H
    rw [F3T_ByteCarrier.lift_eval]
    exact ARX_SubmissionBudget.bound native1 copy allocator CPH_Program.verifier a (Q0+Q1) queries H
  have numeric := add_le_add (F3T_ModelClaims.failure_bound D
    (F3T_ByteCarrier.lift cfg (submission a)) (Q0+Q1) lifted)
    (le_refl (F3T_Numeric.accountLoss (Q0+Q1)))
  rw [F3T_Combined.arithmetic] at numeric
  unfold F3T_ModelClaims.failure at numeric
  change lazyMean (F3U_Joint.program runtime recorder model) emptyTable
    (fun v => max (F3T_Runtime.runtimeMass v.2.1)
      (AspisV8R19.CausalFirstHitUnionBound.indicator (event v.2.2.1))) + _ ≤ _
  linarith

#print axioms bound
end AspisR1.NNC_RecordedEnvelope
end

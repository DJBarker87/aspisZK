import RawChecksAdaptiveCleanModel
import RawChecksAdaptiveInjection
import RawRecordedActualAdaptiveFailureBoundV6

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace AspisR1.RawChecksAdaptiveFailureNoModel

open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound
open AspisR1.RawCutProverCompiler
open AspisR1.RawCutWordsFromView
open AspisR1.RawCutTranscriptRun
open AspisR1.RawAdaptiveDecoderInjection
open AspisR1.RawAdaptiveLiteralDecoder
open AspisR1.RawAdaptiveClassifierHitDensity
open AspisR1.DecodedFirstReadUnionBound
open AspisR1.GenericNoHit
open AspisR1.RawRecordedOracleExtractionMass
open AspisR1.RawRecordedActualAdaptiveFailureBound

abbrev Bytes := AspisV8R19.DuplexFrames.Bytes
abbrev State := AspisV8R19.SourceDuplexStep.State

/-- Derive the recorded-run clean-model condition from checked acceptance,
then apply the established shared-oracle collision, decoded-start, and bank
abort bound. The original first-read budget, fixed public tag, terminal-checks
implication, and decoded-start bound remain explicit. -/
theorem checked_acceptance_failure_bound_no_model
    (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover)
    (Q N : Nat)
    (hQ : ∀ H : Bytes → State, firstReads emptyTable
      (eval H (experiment P (verifier decoder d))).1 ≤ Q)
    (htag : ∀ H : Bytes → State,
      (eval H (experiment P (verifier decoder d))).2.1.1.tag = 2)
    (hchecks : ∀ H : Bytes → State,
      FS2.accepts (eval H (experiment P (verifier decoder d))) →
      LiteralAcceptanceTerminal.Checks
        (eval H (experiment
          (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
          (verifier decoder d))).2.1.1
        (((LiteralByteProtocol.protocol decoder).transcript H
          (eval H (experiment
            (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
            (verifier decoder d))).2.1.1
          (eval H (experiment
            (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
            (verifier decoder d))).2.1.2 33).rounds))
    (hN : ∀ H : Bytes → State, decoderFirstReads
      (RawAdaptiveLiteralDecoder.decode RawFullPublicSelection.select
        LiteralTableWordChoice.choose) emptyTable
      (eval H (AcceptedAdaptiveFiatShamir.experiment
        (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
        (verifier decoder d))).1 ≤ N) :
    lazyMean
      (AcceptedAdaptiveFiatShamir.experiment
        (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
        (verifier decoder d)) emptyTable failureMass ≤
      (kappa Q) + (N : ℚ) * PerAttemptEnvelope.B + (1 / (2 : ℚ)^126) := by
  let inj := RawChecksAdaptiveInjection.injection_of_checked_acceptance
    decoder d P Q hQ htag hchecks
  let exp := AcceptedAdaptiveFiatShamir.experiment
    (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
    (verifier decoder d)
  let hit : RunView → Prop := fun run =>
    inj.Coll run ∨ hitsChain3
      (RawAdaptiveLiteralDecoder.decode RawFullPublicSelection.select
        LiteralTableWordChoice.choose)
      RawAdaptiveClassifierHitDensity.classifier emptyTable run.1
  have hm : CleanAcceptedModel decoder exp hit := by
    exact RawChecksAdaptiveCleanModel.clean_model_of_checked_acceptance_no_hit
      decoder d P Q hchecks inj exp rfl hit (fun _ => Iff.rfl)
  exact RawRecordedActualAdaptiveFailureBound.actual_recorded_failure_le_collision_add_start_density_add_abort
    decoder RawFullPublicSelection.select LiteralTableWordChoice.choose
    (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
    (verifier decoder d) kappa Q N inj hm hN

#print axioms checked_acceptance_failure_bound_no_model
end AspisR1.RawChecksAdaptiveFailureNoModel
end

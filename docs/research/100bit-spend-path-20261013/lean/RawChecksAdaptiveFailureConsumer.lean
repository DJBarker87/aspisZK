import RawChecksAdaptiveInjection
import RawRecordedActualAdaptiveFailureBoundV6

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace AspisR1.RawChecksAdaptiveFailureConsumer

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

/-- Consume checked acceptance in the compiler annotation directly into the
actual adaptive-injection/shared-oracle failure theorem.  Transcript no-hit
remains the exact `CleanAcceptedModel` source-alignment premise; this wrapper
does not identify fresh-process and shared-ROM experiments. -/
theorem checked_acceptance_failure_bound
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
        (verifier decoder d))).1 ≤ N)
    (hmodel : CleanAcceptedModel decoder
      (AcceptedAdaptiveFiatShamir.experiment
        (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
        (verifier decoder d))
      (fun run => collision Q run ∨ hitsChain3
        (RawAdaptiveLiteralDecoder.decode RawFullPublicSelection.select
          LiteralTableWordChoice.choose)
        RawAdaptiveClassifierHitDensity.classifier emptyTable run.1)) :
    lazyMean
      (AcceptedAdaptiveFiatShamir.experiment
        (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
        (verifier decoder d)) emptyTable failureMass ≤
      (kappa Q) + (N : ℚ) * PerAttemptEnvelope.B + (1 / (2 : ℚ)^126) := by
  let inj := RawChecksAdaptiveInjection.injection_of_checked_acceptance
    decoder d P Q hQ htag hchecks
  have hm : CleanAcceptedModel decoder
      (AcceptedAdaptiveFiatShamir.experiment
        (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
        (verifier decoder d))
      (fun run => inj.Coll run ∨ hitsChain3
        (RawAdaptiveLiteralDecoder.decode RawFullPublicSelection.select
          LiteralTableWordChoice.choose)
        RawAdaptiveClassifierHitDensity.classifier emptyTable run.1) := by
    intro H
    dsimp only [inj, RawChecksAdaptiveInjection.injection_of_checked_acceptance,
      RawAdaptiveDecoderInjection.injection]
    exact hmodel H
  exact RawRecordedActualAdaptiveFailureBound.actual_recorded_failure_le_collision_add_start_density_add_abort
    decoder RawFullPublicSelection.select LiteralTableWordChoice.choose
    (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
    (verifier decoder d) kappa Q N inj hm hN

#print axioms checked_acceptance_failure_bound
end AspisR1.RawChecksAdaptiveFailureConsumer
end

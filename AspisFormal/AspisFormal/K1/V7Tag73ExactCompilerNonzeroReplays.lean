import AspisFormal.K1.V7Tag73AcceptedSemanticExecution
import AspisFormal.K1.V7Tag73ExactCompilerNonzeroEventReplay

/-!
# Production replay for all four nonzero samplers

The accepted Tag-73 schedule has four nonzero QM31 challenges: eta, gamma,
kappa, and queryBatch.  This file packages exact cache-aware source replays
for all four from the literal pre- and post-q16 event lists.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCompilerNonzeroReplays

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AcceptedSemanticExecution
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerNonzeroEventReplay
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

structure ExactCompilerNonzeroReplays
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Prop where
  eta : ExactCompilerNonzeroReplayAt input .eta
  gamma : ExactCompilerNonzeroReplayAt input .gamma
  kappa : ExactCompilerNonzeroReplayAt input .kappa
  queryBatch : ExactCompilerNonzeroReplayAt input .queryBatch

theorem exact_compiler_nonzero_replays
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ExactCompilerNonzeroReplays input := by
  obtain ⟨evaluator⟩ :=
    exact_operational_input_constructs_complete_evaluator input
  have finalDecoded := exact_operational_input_final_samples_decode input
    evaluator
  have prefixIncluded : SamplesIncluded evaluator.prefixState
      evaluator.finalState :=
    samples_included_trans
      (run_q16_preserves_prior_samples (exactOperationalTable input)
        evaluator.prefixState evaluator.afterQ16
          (q16TapeOfSearch (exactOperationalTape input).search) evaluator.q16Run)
      (machine_events_work_erased_samples_included
        (exactOperationalTable input)
          (afterAcceptedQueryScan (exactOperationalTape input).messages)
            evaluator.afterQ16 evaluator.finalState evaluator.afterQ16Run)
  have prefixDecoded : StateSamplesDecodeAs
      (exactOperationalTape input).messages evaluator.prefixState :=
    state_samples_decode_of_included (exactOperationalTape input).messages
      evaluator.prefixState evaluator.finalState prefixIncluded finalDecoded
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply exact_compiler_actual_nonzero_event_replay_at transitionRoom input
      (prefixAfterC2 (exactOperationalTape input).messages)
      evaluator.afterC2 evaluator.prefixState .eta
      ((exactOperationalTape input).messages.challengeUse .eta) (by rfl)
    · simp [prefixAfterC2, semanticEvents, challengeEvent]
    · exact evaluator.beforeQ16Run
    · exact prefixDecoded
  · apply exact_compiler_actual_nonzero_event_replay_at transitionRoom input
      (prefixAfterC2 (exactOperationalTape input).messages)
      evaluator.afterC2 evaluator.prefixState .gamma
      ((exactOperationalTape input).messages.challengeUse .gamma) (by rfl)
    · simp [prefixAfterC2, semanticEvents, challengeEvent]
    · exact evaluator.beforeQ16Run
    · exact prefixDecoded
  · apply exact_compiler_actual_nonzero_event_replay_at transitionRoom input
      (prefixAfterC2 (exactOperationalTape input).messages)
      evaluator.afterC2 evaluator.prefixState .kappa
      ((exactOperationalTape input).messages.challengeUse .kappa) (by rfl)
    · simp [prefixAfterC2, semanticEvents, challengeEvent]
    · exact evaluator.beforeQ16Run
    · exact prefixDecoded
  · apply exact_compiler_actual_nonzero_event_replay_at transitionRoom input
      (afterAcceptedQueryScan (exactOperationalTape input).messages)
      evaluator.afterQ16 evaluator.finalState .queryBatch
      ((exactOperationalTape input).messages.challengeUse .queryBatch) (by rfl)
    · simp [afterAcceptedQueryScan, challengeEvent]
    · exact evaluator.afterQ16Run
    · exact finalDecoded

#print axioms ExactCompilerNonzeroReplays
#print axioms exact_compiler_nonzero_replays

end
end AspisK1.V7Tag73ExactCompilerNonzeroReplays

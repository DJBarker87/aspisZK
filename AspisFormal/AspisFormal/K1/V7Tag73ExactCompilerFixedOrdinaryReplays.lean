import AspisFormal.K1.V7Tag73ExactCompilerOrdinaryEventReplay
import AspisFormal.K1.V7Tag73ExactCompilerSemanticOrdinaryReplay

/-!
# Production replay for the remaining fixed ordinary samplers

This packages lambda, chi, mu, and both OOD-mix ordinary challenges.  These
are the ordinary challenge values used by the six non-semantic fixed K1.5
families; kappa remains a nonzero-sampler case and is deliberately separate.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCompilerFixedOrdinaryReplays

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AcceptedSemanticExecution
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerOrdinaryEventReplay
open AspisK1.V7Tag73ExactCompilerSemanticOrdinaryReplay
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

structure ExactCompilerFixedOrdinaryReplays
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
  lambda : ExactCompilerOrdinaryReplayAt input .lambda
  chi : ExactCompilerOrdinaryReplayAt input .chi
  mu : ExactCompilerOrdinaryReplayAt input .mu
  oodMix : ∀ sample : Fin 2,
    ExactCompilerOrdinaryReplayAt input (.oodMix sample)

theorem exact_compiler_fixed_ordinary_replays
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
    ExactCompilerFixedOrdinaryReplays input := by
  obtain ⟨evaluator⟩ :=
    exact_operational_input_constructs_complete_evaluator input
  obtain ⟨segments⟩ := complete_evaluator_exposes_semantic_segments
    (exactOperationalTable input) (exactOperationalTape input)
      (exactOperationalRawTrace input) evaluator
  have finalDecoded := exact_operational_input_final_samples_decode input
    evaluator
  have lambdaDecoded : StateSamplesDecodeAs
      (exactOperationalTape input).messages evaluator.afterLambda :=
    state_samples_decode_of_included (exactOperationalTape input).messages
      evaluator.afterLambda evaluator.finalState
        (evaluator_afterLambda_samples_included_final
          (exactOperationalTable input) (exactOperationalTape input)
            (exactOperationalRawTrace input) evaluator)
          finalDecoded
  have chiDecoded : StateSamplesDecodeAs
      (exactOperationalTape input).messages evaluator.afterPhaseChallenges :=
    state_samples_decode_of_included (exactOperationalTape input).messages
      evaluator.afterPhaseChallenges evaluator.finalState
        (evaluator_afterPhase_samples_included_final
          (exactOperationalTable input) (exactOperationalTape input)
            (exactOperationalRawTrace input) evaluator)
          finalDecoded
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
  have lambdaListRun : runMachineEventsWorkErased
      (exactOperationalTable input)
      [challengeEvent (exactOperationalTape input).messages .lambda]
      evaluator.afterC1 = some evaluator.afterLambda := by
    simp [runMachineEventsWorkErased, evaluator.lambdaRun]
  have chiListRun : runMachineEventsWorkErased
      (exactOperationalTable input)
      [challengeEvent (exactOperationalTape input).messages .chi]
      evaluator.afterLambda = some evaluator.afterPhaseChallenges := by
    simp [runMachineEventsWorkErased, evaluator.chiRun]
  have semanticReplays :=
    exact_compiler_all_semantic_ordinary_replays transitionRoom input
  refine ⟨?_, ?_, semanticReplays .mu, ?_⟩
  · exact exact_compiler_actual_ordinary_event_replay_at transitionRoom input
      [challengeEvent (exactOperationalTape input).messages .lambda]
      evaluator.afterC1 evaluator.afterLambda .lambda
      ((exactOperationalTape input).messages.challengeUse .lambda)
      (by rfl) (by simp [challengeEvent]) lambdaListRun lambdaDecoded
  · exact exact_compiler_actual_ordinary_event_replay_at transitionRoom input
      [challengeEvent (exactOperationalTape input).messages .chi]
      evaluator.afterLambda evaluator.afterPhaseChallenges .chi
      ((exactOperationalTape input).messages.challengeUse .chi)
      (by rfl) (by simp [challengeEvent]) chiListRun chiDecoded
  · intro oodSample
    apply exact_compiler_actual_ordinary_event_replay_at transitionRoom input
      (afterSemanticTailEvents (exactOperationalTape input).messages)
      segments.afterSemantic evaluator.prefixState (.oodMix oodSample)
      ((exactOperationalTape input).messages.challengeUse (.oodMix oodSample))
      (by rfl)
    · fin_cases oodSample <;>
        simp [afterSemanticTailEvents, oodEvents, challengeEvent]
    · exact segments.afterSemanticRun
    · exact prefixDecoded

#print axioms ExactCompilerFixedOrdinaryReplays
#print axioms exact_compiler_fixed_ordinary_replays

end
end AspisK1.V7Tag73ExactCompilerFixedOrdinaryReplays

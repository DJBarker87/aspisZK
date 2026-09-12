import SuccessfulReplayAlphaDisposition
import FSV8ReplayConfigurationExactness

/-!
# Total disposition of a selected alpha replay configuration

This leaf compares an arbitrary restoration configuration with the literal
alpha boundary constructed by the same successful replay.  The aligned case
retains the exhaustive live target disposition; the mismatched case retains
the exact input inequality.  No chronology or target probability claim is
made beyond the actual-boundary witness supplied by the replay.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 1400

namespace AspisV8Completion.SuccessfulReplayAlphaConfigurationDisposition

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open FSV8PostOODGammaScript
open ExtractionCollectorSuccessfulReplay
open SuccessfulReplayAlphaBoundary
open SuccessfulReplayAlphaDisposition
open FSV8AlphaChallengeInputBridge
open FSV8ReplayConfigurationExactness

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K

noncomputable section

inductive AlphaConfigurationDisposition
    {TapeIdentity Observation Statement Proof Result : Type*}
    {n m : Nat} {z : Fin 10 → K}
    {cuts : FSBoundedTranscript.RootCuts} {initialDigest : Block}
    {firstWork : Point → Script Bytes Block Unit n}
    {secondWork : Point → Point → Script Bytes Block Unit m}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Result)
    (replay : SuccessfulReplay z cuts initialDigest firstWork secondWork)
    (configuration : OriginReplayConfiguration) : Prop where
  | aligned
      (afterAlphaNonce : FSBoundedTranscript.Transcript)
      (actual : IsActualAlphaBoundary replay afterAlphaNonce)
      (configurationEq :
        configuration = alphaBoundaryConfiguration afterAlphaNonce
          configuration.firstRunUse configuration.forkOutput
          configuration.postForkController configuration.oracleLimits
          configuration.budget configuration.replayFuel)
      (live : LiveAlphaDisposition origin afterAlphaNonce
        configuration.firstRunUse configuration.forkOutput
        configuration.postForkController configuration.oracleLimits
        configuration.budget configuration.replayFuel)
  | mismatched
      (afterAlphaNonce : FSBoundedTranscript.Transcript)
      (actual : IsActualAlphaBoundary replay afterAlphaNonce)
      (inputNe : configuration.transcriptDrivingInput ≠
        alphaCandidateInput afterAlphaNonce)

theorem successful_replay_configuration_disposition
    {TapeIdentity Observation Statement Proof Result : Type*}
    {n m : Nat} {z : Fin 10 → K}
    {cuts : FSBoundedTranscript.RootCuts} {initialDigest : Block}
    {firstWork : Point → Script Bytes Block Unit n}
    {secondWork : Point → Point → Script Bytes Block Unit m}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Result)
    (replay : SuccessfulReplay z cuts initialDigest firstWork secondWork)
    (configuration : OriginReplayConfiguration) :
    AlphaConfigurationDisposition origin replay configuration := by
  obtain ⟨afterAlphaNonce, actual, live⟩ :=
    successful_replay_constructs_live_alpha_disposition origin replay
      configuration.firstRunUse configuration.forkOutput
      configuration.postForkController configuration.oracleLimits
      configuration.budget configuration.replayFuel
  by_cases inputEq : configuration.transcriptDrivingInput =
      alphaCandidateInput afterAlphaNonce
  · have configurationEq :=
      (configuration_eq_alphaBoundaryConfiguration_iff configuration
        afterAlphaNonce).2 inputEq
    exact AlphaConfigurationDisposition.aligned
      (origin := origin) (replay := replay) (configuration := configuration)
      afterAlphaNonce actual configurationEq live
  · exact AlphaConfigurationDisposition.mismatched
      (origin := origin) (replay := replay) (configuration := configuration)
      afterAlphaNonce actual inputEq

#print axioms successful_replay_configuration_disposition

end
end AspisV8Completion.SuccessfulReplayAlphaConfigurationDisposition

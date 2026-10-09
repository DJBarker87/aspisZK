import SuccessfulReplayAlphaBoundary
import FSV8AlphaTargetRestorationAdapter

/-!
# Total alpha-target disposition at an actual successful replay boundary

The earlier target classifier accepted an arbitrary `afterAlphaNonce`. This
leaf applies it only to a transcript state constructed from an actual
successful same-body replay. In the prior-adversary branch it also constructs
the exact fixed-record membership needed by the start-only replay algorithm.

No probability is assigned here. Prior-table and absent targets remain
visible alternatives for the global Fiat--Shamir argument.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000

namespace AspisV8Completion.SuccessfulReplayAlphaDisposition

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open FSV8PostOODGammaScript
open ExtractionCollectorSuccessfulReplay
open SuccessfulReplayAlphaBoundary
open FSV8AlphaChallengeInputBridge
open FSV8AlphaTargetDisposition
open FSV8AlphaTargetRestorationAdapter

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K

noncomputable section

/-- Exhaustive classification of the actual alpha target relative to the
frozen adversary state. The prior-adversary constructor contains the exact
membership and driving-input equality consumed by `constructLegalReplay`;
the other two constructors deliberately remain uncharged. -/
inductive LiveAlphaDisposition
    {TapeIdentity Observation Statement Proof Result : Type*}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Result)
    (afterAlphaNonce : FSBoundedTranscript.Transcript)
    (firstRunUse : ResourceUse) (forkOutput : ShaOutput)
    (postForkController : AdaptiveController) (oracleLimits : OracleLimits)
    (budget : ResourceBudget) (replayFuel : Nat) : Prop where
  | priorAdversary
      (record : QueryRecord)
      (member : record ∈
        (fixedFirstRunRecordFromOrigin origin
          (alphaBoundaryConfiguration afterAlphaNonce firstRunUse forkOutput
            postForkController oracleLimits budget replayFuel)).firstRun.q1)
      (drivingInput :
        (fixedFirstRunRecordFromOrigin origin
          (alphaBoundaryConfiguration afterAlphaNonce firstRunUse forkOutput
            postForkController oracleLimits budget replayFuel)).transcriptDrivingInput =
          record.input)
  | priorTarget
      (entry : TableEntry)
      (lookup : lookupEntry origin.firstRun.stateAtAdversaryHalt
        (alphaCandidateInput afterAlphaNonce) = some entry)
  | absent
      (lookup : lookupEntry origin.firstRun.stateAtAdversaryHalt
        (alphaCandidateInput afterAlphaNonce) = none)

/-- The source target classifier constructs the complete live disposition.
No candidate membership, replay success, or freshness branch is assumed. -/
theorem live_alpha_disposition
    {TapeIdentity Observation Statement Proof Result : Type*}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Result)
    (afterAlphaNonce : FSBoundedTranscript.Transcript)
    (firstRunUse : ResourceUse) (forkOutput : ShaOutput)
    (postForkController : AdaptiveController) (oracleLimits : OracleLimits)
    (budget : ResourceBudget) (replayFuel : Nat) :
    LiveAlphaDisposition origin afterAlphaNonce firstRunUse forkOutput
      postForkController oracleLimits budget replayFuel := by
  cases alpha_target_disposition origin.firstRun.stateAtAdversaryHalt
      afterAlphaNonce with
  | priorAdversaryQ1 record member inputEq =>
      obtain ⟨fixedMember, drivingInput⟩ := prior_q1_supplies_fixed_record
        origin afterAlphaNonce firstRunUse forkOutput postForkController
        oracleLimits budget replayFuel record member inputEq
      exact .priorAdversary record fixedMember drivingInput
  | priorTarget entry lookup =>
      exact .priorTarget entry lookup
  | absent lookup =>
      exact .absent lookup

/-- A successful selected replay constructs both its literal pre-alpha state
and the exhaustive target disposition at that exact state. -/
theorem successful_replay_constructs_live_alpha_disposition
    {TapeIdentity Observation Statement Proof Result : Type*}
    {n m : Nat} {z : Fin 10 → K}
    {cuts : FSBoundedTranscript.RootCuts} {initialDigest : Block}
    {firstWork : Point → Script Bytes Block Unit n}
    {secondWork : Point → Point → Script Bytes Block Unit m}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Result)
    (replay : SuccessfulReplay z cuts initialDigest firstWork secondWork)
    (firstRunUse : ResourceUse) (forkOutput : ShaOutput)
    (postForkController : AdaptiveController) (oracleLimits : OracleLimits)
    (budget : ResourceBudget) (replayFuel : Nat) :
    ∃ afterAlphaNonce,
      IsActualAlphaBoundary replay afterAlphaNonce ∧
      LiveAlphaDisposition origin afterAlphaNonce firstRunUse forkOutput
        postForkController oracleLimits budget replayFuel := by
  obtain ⟨afterAlphaNonce, actual⟩ :=
    successful_replay_constructs_actual_alpha_boundary replay
  exact ⟨afterAlphaNonce, actual,
    live_alpha_disposition origin afterAlphaNonce firstRunUse forkOutput
      postForkController oracleLimits budget replayFuel⟩

#print axioms live_alpha_disposition
#print axioms successful_replay_constructs_live_alpha_disposition

end
end AspisV8Completion.SuccessfulReplayAlphaDisposition

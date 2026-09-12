import FSV8GammaChallengeInputBridge
import FSLiveSourceFunctionalMiddle

/-!
# Exact alpha0 candidate input for state-restoration forks

The first alpha0 candidate is not identified by a role name alone.  Its
actual random-oracle input is the digest after absorbing response0 and the
alpha nonce, followed by the nonzero-candidate squeeze tag.  This leaf derives
that byte string from the real `candidateScript` and constructs the replay
configuration from it.

It does not construct `afterAlphaNonce` from a completed body run and does not
claim that the first-run adversary queried this input.  Those are the next
chronological source obligations.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000

namespace AspisV8Completion.FSV8AlphaChallengeInputBridge

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSNonzeroQM31
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open FSV8GammaChallengeInputBridge

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape

noncomputable section

def alphaCandidateInput (afterAlphaNonce : FSBoundedTranscript.Transcript) : Bytes :=
  List.ofFn afterAlphaNonce.digest ++ [1]

theorem alpha_candidateScript_first_input
    (afterAlphaNonce : FSBoundedTranscript.Transcript) :
    firstScriptInput (candidateScript afterAlphaNonce.digest) =
      some (alphaCandidateInput afterAlphaNonce) := by
  rfl

theorem alpha_candidate_query_mem
    (tape : Tape) (afterAlphaNonce : FSBoundedTranscript.Transcript) :
    ∃ event,
      event.input = alphaCandidateInput afterAlphaNonce ∧
      event ∈ (run tape (candidateScript afterAlphaNonce.digest)
        afterAlphaNonce.oracle).2.log := by
  simpa [alphaCandidateInput, gammaCandidateInput] using
    candidate_query_mem tape afterAlphaNonce

def alphaBoundaryConfiguration
    (afterAlphaNonce : FSBoundedTranscript.Transcript)
    (firstRunUse : ResourceUse) (forkOutput : ShaOutput)
    (postForkController : AdaptiveController) (oracleLimits : OracleLimits)
    (budget : ResourceBudget) (replayFuel : Nat) : OriginReplayConfiguration where
  firstRunUse := firstRunUse
  transcriptDrivingInput := alphaCandidateInput afterAlphaNonce
  forkOutput := forkOutput
  postForkController := postForkController
  oracleLimits := oracleLimits
  budget := budget
  replayFuel := replayFuel

theorem alphaBoundaryConfiguration_input
    (afterAlphaNonce : FSBoundedTranscript.Transcript)
    (firstRunUse : ResourceUse) (forkOutput : ShaOutput)
    (postForkController : AdaptiveController) (oracleLimits : OracleLimits)
    (budget : ResourceBudget) (replayFuel : Nat) :
    (alphaBoundaryConfiguration afterAlphaNonce firstRunUse forkOutput
      postForkController oracleLimits budget replayFuel).transcriptDrivingInput =
      List.ofFn afterAlphaNonce.digest ++ [1] := by
  rfl

/-- Varying only the programmed alpha output leaves every configuration field
that determines the replay before the driving query unchanged.  This theorem
does not yet prove equality of the derived pauses; that must be obtained from
the operational replay constructor rather than inferred from record values. -/
theorem alphaBoundaryConfiguration_fixed_controls
    (afterAlphaNonce : FSBoundedTranscript.Transcript)
    (firstRunUse : ResourceUse) (left right : ShaOutput)
    (postForkController : AdaptiveController) (oracleLimits : OracleLimits)
    (budget : ResourceBudget) (replayFuel : Nat) :
    let l := alphaBoundaryConfiguration afterAlphaNonce firstRunUse left
      postForkController oracleLimits budget replayFuel
    let r := alphaBoundaryConfiguration afterAlphaNonce firstRunUse right
      postForkController oracleLimits budget replayFuel
    l.firstRunUse = r.firstRunUse ∧
      l.transcriptDrivingInput = r.transcriptDrivingInput ∧
      l.postForkController = r.postForkController ∧
      l.oracleLimits = r.oracleLimits ∧
      l.budget = r.budget ∧
      l.replayFuel = r.replayFuel := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem fixedRecord_q1_contains_alpha
    {TapeIdentity Observation Statement Proof Returned : Type*}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Returned)
    (afterAlphaNonce : FSBoundedTranscript.Transcript)
    (firstRunUse : ResourceUse) (forkOutput : ShaOutput)
    (postForkController : AdaptiveController) (oracleLimits : OracleLimits)
    (budget : ResourceBudget) (replayFuel : Nat)
    (event : QueryRecord)
    (eventMem : event ∈ origin.firstRun.stateAtAdversaryHalt.history)
    (eventActor : event.actor = .adversary)
    (eventInput : event.input = alphaCandidateInput afterAlphaNonce) :
    event ∈ (fixedFirstRunRecordFromOrigin origin
      (alphaBoundaryConfiguration afterAlphaNonce firstRunUse forkOutput
        postForkController oracleLimits budget replayFuel)).firstRun.q1 ∧
    (fixedFirstRunRecordFromOrigin origin
      (alphaBoundaryConfiguration afterAlphaNonce firstRunUse forkOutput
        postForkController oracleLimits budget replayFuel)).transcriptDrivingInput =
      event.input := by
  let fixed := fixedFirstRunRecordFromOrigin origin
    (alphaBoundaryConfiguration afterAlphaNonce firstRunUse forkOutput
      postForkController oracleLimits budget replayFuel)
  have stateMem : event ∈ fixed.firstRun.stateAtAdversaryHalt.history := by
    dsimp [fixed]
    simpa using eventMem
  constructor
  · change event ∈ fixed.firstRun.q1
    unfold FirstRun.q1 freezeAdversaryQ1
    exact List.mem_filter.mpr ⟨stateMem, by simp [eventActor]⟩
  · change (alphaBoundaryConfiguration afterAlphaNonce firstRunUse forkOutput
      postForkController oracleLimits budget replayFuel).transcriptDrivingInput =
      event.input
    rw [alphaBoundaryConfiguration_input]
    exact eventInput.symm

#print axioms alpha_candidateScript_first_input
#print axioms alpha_candidate_query_mem
#print axioms alphaBoundaryConfiguration_fixed_controls
#print axioms fixedRecord_q1_contains_alpha

end
end AspisV8Completion.FSV8AlphaChallengeInputBridge

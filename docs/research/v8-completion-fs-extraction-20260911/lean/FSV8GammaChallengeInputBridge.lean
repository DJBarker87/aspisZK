import FSV8PostOODGammaScript
import AspisFormal.K1.V7FsStateRestorationCoupling
import ExtractionCollectorReplayableSource

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8GammaChallengeInputBridge
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSV8PostOODGammaScript FSNonzeroQM31
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open ExtractionCollectorReplayableSource

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Observation := ExtractionCollectorReplayableSource.Observation
abbrev Returned := ExtractionCollectorReplayableSource.Returned

noncomputable section

/-! The V7 restoration record wants a `ShaInput`.  At the first nonzero
candidate boundary the actual input is the post-label-28 digest followed by
the squeeze tag.  This is computed from the transcript cut, not supplied as
a verifier label. -/
def gammaCandidateInput (afterNonce : FSBoundedTranscript.Transcript) : Bytes :=
  List.ofFn afterNonce.digest ++ [1]

def firstScriptInput {A : Type} : {n : Nat} → Script Bytes Block A n → Option Bytes
  | _, .done _ => none
  | _, .abort => none
  | _, .ask input _ => some input

theorem candidateScript_first_input (digest : Block) :
    firstScriptInput (FSNonzeroQM31.candidateScript digest) =
      some (List.ofFn digest ++ [1]) := by
  rfl

theorem run_ask_input_mem {A : Type} (tape : Tape) {n : Nat} (input : Bytes)
    (next : Block → Script Bytes Block A n)
    (oracle : FSOracleExecution.State Bytes Block) :
    ∃ event,
      event.input = input ∧
      event ∈ (run tape (.ask input next) oracle).2.log := by
  obtain ⟨event, eventLog, eventInput, _⟩ := query_log tape oracle input
  obtain ⟨tail, tailLog⟩ := run_extends tape (next (query tape oracle input).1)
    (query tape oracle input).2
  refine ⟨event, eventInput, ?_⟩
  simp only [run, eventLog, tailLog]
  simp

theorem candidate_query_mem
    (tape : Tape) (afterNonce : FSBoundedTranscript.Transcript) :
    ∃ event,
      event.input = gammaCandidateInput afterNonce ∧
      event ∈ (run tape
        (FSNonzeroQM31.candidateScript afterNonce.digest)
        afterNonce.oracle).2.log := by
  generalize hs : FSNonzeroQM31.candidateScript afterNonce.digest = script
  cases script with
  | done value =>
      simp [FSNonzeroQM31.candidateScript,
        FSTranscriptScript.challengeScript, FSTranscriptScript.squeezeScript] at hs
      cases hs
  | abort =>
      simp [FSNonzeroQM31.candidateScript,
        FSTranscriptScript.challengeScript, FSTranscriptScript.squeezeScript] at hs
      cases hs
  | ask input next =>
      simp [FSNonzeroQM31.candidateScript,
        FSTranscriptScript.challengeScript, FSTranscriptScript.squeezeScript,
        FSTranscriptScript.bind] at hs
      have hmem := run_ask_input_mem tape input next afterNonce.oracle
      refine ⟨hmem.choose, ?_, hmem.choose_spec.2⟩
      rw [hmem.choose_spec.1]
      simpa [gammaCandidateInput] using hs.1.symm

theorem candidate_prefix
    (tape : Tape) (afterNonce : FSBoundedTranscript.Transcript) :
    FSBoundedTranscript.Prefix afterNonce.oracle
      (run tape (FSNonzeroQM31.candidateScript afterNonce.digest)
        afterNonce.oracle).2 := by
  obtain ⟨suffix, h⟩ := run_extends tape
    (FSNonzeroQM31.candidateScript afterNonce.digest) afterNonce.oracle
  exact ⟨suffix, h⟩

structure GammaCandidateEvidence (tape : Tape)
    (afterNonce : FSBoundedTranscript.Transcript) where
  input : Bytes
  input_eq : input = gammaCandidateInput afterNonce
  event : FSOracleExecution.Event Bytes Block
  event_input : event.input = input
  event_mem : event ∈
    (run tape (FSNonzeroQM31.candidateScript afterNonce.digest)
      afterNonce.oracle).2.log
  prefixProof : FSBoundedTranscript.Prefix afterNonce.oracle
    (run tape (FSNonzeroQM31.candidateScript afterNonce.digest)
      afterNonce.oracle).2

def gammaCandidateEvidence (tape : Tape)
    (afterNonce : FSBoundedTranscript.Transcript) :
    GammaCandidateEvidence tape afterNonce :=
  let mem := candidate_query_mem tape afterNonce
  let pref := candidate_prefix tape afterNonce
  { input := gammaCandidateInput afterNonce
    input_eq := rfl
    event := mem.choose
    event_input := mem.choose_spec.1
    event_mem := mem.choose_spec.2
    prefixProof := pref }

/-! This constructor fixes the V7 driving input from the actual gamma
candidate boundary while deliberately leaving fork output and all resource
controls explicit.  It is therefore a boundary adapter, not a restoration
success claim. -/
def gammaBoundaryConfiguration
    (afterNonce : FSBoundedTranscript.Transcript)
    (firstRunUse : ResourceUse) (forkOutput : ShaOutput)
    (postForkController : AdaptiveController) (oracleLimits : OracleLimits)
    (budget : ResourceBudget) (replayFuel : Nat) : OriginReplayConfiguration where
  firstRunUse := firstRunUse
  transcriptDrivingInput := gammaCandidateInput afterNonce
  forkOutput := forkOutput
  postForkController := postForkController
  oracleLimits := oracleLimits
  budget := budget
  replayFuel := replayFuel

theorem gammaBoundaryConfiguration_input
    (afterNonce : FSBoundedTranscript.Transcript)
    (firstRunUse : ResourceUse) (forkOutput : ShaOutput)
    (postForkController : AdaptiveController) (oracleLimits : OracleLimits)
    (budget : ResourceBudget) (replayFuel : Nat) :
    (gammaBoundaryConfiguration afterNonce firstRunUse forkOutput
      postForkController oracleLimits budget replayFuel).transcriptDrivingInput =
      List.ofFn afterNonce.digest ++ [1] := by
  rfl

/-! The V7 side can consume the computed input once its actual origin history
contains the corresponding adversary query.  This theorem exposes precisely
that remaining history-to-origin obligation; it does not postulate it. -/
theorem fixedRecord_q1_contains_gamma
    {TapeIdentity Statement Proof : Type*}
    (origin : SameTapeExperimentOrigin TapeIdentity Observation Statement Proof Returned)
    (afterNonce : FSBoundedTranscript.Transcript)
    (firstRunUse : ResourceUse) (forkOutput : ShaOutput)
    (postForkController : AdaptiveController) (oracleLimits : OracleLimits)
    (budget : ResourceBudget) (replayFuel : Nat)
    (event : QueryRecord)
    (eventMem : event ∈ origin.firstRun.stateAtAdversaryHalt.history)
    (eventActor : event.actor = .adversary)
    (eventInput : event.input = gammaCandidateInput afterNonce) :
    event ∈ (fixedFirstRunRecordFromOrigin origin
      (gammaBoundaryConfiguration afterNonce firstRunUse forkOutput
        postForkController oracleLimits budget replayFuel)).firstRun.q1 ∧
    (fixedFirstRunRecordFromOrigin origin
      (gammaBoundaryConfiguration afterNonce firstRunUse forkOutput
        postForkController oracleLimits budget replayFuel)).transcriptDrivingInput =
      event.input := by
  let fixed := fixedFirstRunRecordFromOrigin origin
    (gammaBoundaryConfiguration afterNonce firstRunUse forkOutput
      postForkController oracleLimits budget replayFuel)
  have stateMem : event ∈ fixed.firstRun.stateAtAdversaryHalt.history := by
    dsimp [fixed]
    simpa using eventMem
  constructor
  · change event ∈ fixed.firstRun.q1
    unfold FirstRun.q1 freezeAdversaryQ1
    refine List.mem_filter.mpr ⟨stateMem, ?_⟩
    simp [eventActor]
  · change (gammaBoundaryConfiguration afterNonce firstRunUse forkOutput
      postForkController oracleLimits budget replayFuel).transcriptDrivingInput =
      event.input
    rw [gammaBoundaryConfiguration_input]
    exact eventInput.symm

theorem gammaCandidateEvidence_input_is_actual_query
    (tape : Tape) (afterNonce : FSBoundedTranscript.Transcript) :
    (gammaCandidateEvidence tape afterNonce).event.input =
      List.ofFn afterNonce.digest ++ [1] := by
  exact (gammaCandidateEvidence tape afterNonce).event_input

#print axioms candidate_query_mem
#print axioms candidate_prefix
#print axioms gammaCandidateEvidence_input_is_actual_query
#print axioms gammaBoundaryConfiguration_input
#print axioms fixedRecord_q1_contains_gamma
end
end AspisV8Completion.FSV8GammaChallengeInputBridge

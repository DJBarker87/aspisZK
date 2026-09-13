import FSV8AlphaFreshCreatorCoverage
import FSV8AcceptedExactRootAlphaMarkerTargetEvent

/-!
# Honest accounting for cached calls in the first alpha pair

There is no preceding alpha advance at the first pair.  Consequently the
later-conflict target theorem cannot be applied to either initial cached case.
This leaf records the exact source facts that are available instead.

* If output is fresh and advance is cached, fresh-creator coverage recovers
  the creator of the cached advance key.  No relation between the fresh output
  answer and that creator input is implied.
* If output is cached, the marker-origin routing already constructed for the
  exact accepted root loses only its impossible `freshAtCandidate` branch.
  Prior-adversary and cached-marker alternatives remain explicit alongside
  the already charged root target event.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 1800

namespace AspisV8Completion.FSV8AlphaInitialCachedCases

open FSBoundedTranscript
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73TranscriptSchedule
open FSV8AlignedAlphaSqueezeStep
open FSV8AlignedAlphaInitialPairDisposition
open FSV8CandidateOriginTrace
open FSV8AlphaFreshCreatorCoverage
open FSV8AlphaTableHistoryCoverage
open FSV8AcceptedExactRootAlphaMarkerTargetEvent

noncomputable section

abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape

private theorem lookup_entry_some_input_and_member_local
    (state : OracleState) (input : ShaInput) (entry : TableEntry)
    (found : lookupEntry state input = some entry) :
    entry.input = input ∧ entry ∈ state.table := by
  unfold lookupEntry at found
  have foundSpec := List.find?_eq_some_iff_append.mp found
  exact ⟨of_decide_eq_true foundSpec.1, List.mem_of_find?_eq_some found⟩

/-- The mixed initial case constructs the real first fresh creator of the
cached advance key.  This is provenance, not target membership. -/
theorem initial_output_fresh_advance_cached_has_fresh_creator
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {v7 : OracleState} {s : Transcript}
    (pair : AlignedSqueezePair tape finiteTape limits v7 s)
    (covered : TableCoveredByFreshHistory v7)
    (disposition : InitialPairDisposition tape finiteTape limits v7 s pair)
    (mixed : ∃ outputOrigin advanceOrigin outputMissing entry advanceFound,
      disposition = .outputFreshAdvanceCached outputOrigin advanceOrigin
        outputMissing entry advanceFound) :
    ∃ creator,
      creator ∈ v7.history ∧ creator.origin = .fresh ∧
      creator.input = advanceInput s := by
  rcases mixed with ⟨outputOrigin, advanceOrigin, outputMissing, entry,
    advanceFound, dispositionExact⟩
  cases dispositionExact
  obtain ⟨entryInput, entryMember⟩ :=
    lookup_entry_some_input_and_member_local v7 (advanceInput s) entry
      advanceFound
  obtain ⟨creator, creatorMember, creatorFresh, creatorInput,
    _creatorOutput⟩ := covered entry entryMember
  exact ⟨creator, creatorMember, creatorFresh,
    creatorInput.trans entryInput⟩

/-- The literal-prefix premise needed to target-route a fresh output answer
against the cached advance key is equivalent to an actual digest equality.
The mixed disposition supplies no such equality. -/
theorem output_answer_prefix_advance_key_iff
    (answer digest : Block) :
    HasLiteralStatePrefix answer (List.ofFn digest ++ [2]) ↔
      answer = digest := by
  constructor
  · intro hprefix
    unfold HasLiteralStatePrefix AspisK1.V7Tag73TranscriptSchedule.bytes at hprefix
    rw [List.take_append_of_le_length (by simp)] at hprefix
    exact List.ofFn_injective hprefix
  · intro hEq
    subst answer
    unfold HasLiteralStatePrefix AspisK1.V7Tag73TranscriptSchedule.bytes
    rw [List.take_append_of_le_length (by simp)]
    simp

/-- Remaining exact-root alternatives after the first alpha output is known
to be cached.  This is the marker disposition with only the contradictory
`freshAtCandidate` case removed. -/
inductive InitialOutputCachedMarkerDisposition
    (root candidateState : OracleState) (candidateInput : ShaInput)
    (rootTargetEvent : Prop) : Prop where
  | priorAdversary
      (record : QueryRecord)
      (member : record ∈ freezeAdversaryQ1 root)
      (inputEq : record.input = candidateInput)
  | rootTarget (event : rootTargetEvent)
  | markerCachedFreshSource
      (markerState : OracleState) (markerInput : ShaInput)
      (markerAnswer : Digest256)
      (target : markerAnswer ∈
        operationalRequestTargets ∅ markerState.history markerInput)
      (entry : TableEntry)
      (found : lookupEntry markerState markerInput = some entry)
      (sourceExact : entry.source = .fresh)
      (outputExact : entry.output = markerAnswer)
  | markerCachedProgrammedSource
      (markerState : OracleState) (markerInput : ShaInput)
      (markerAnswer : Digest256)
      (target : markerAnswer ∈
        operationalRequestTargets ∅ markerState.history markerInput)
      (entry : TableEntry)
      (found : lookupEntry markerState markerInput = some entry)
      (sourceExact : entry.source = .programmed)
      (outputExact : entry.output = markerAnswer)

theorem cached_initial_output_refines_exact_marker_disposition
    (root candidateState : OracleState) (candidateInput : ShaInput)
    (rootTargetEvent : Prop)
    (marker : AlphaMarkerTargetEventDisposition root candidateState
      candidateInput rootTargetEvent)
    (entry : TableEntry)
    (cached : lookupEntry candidateState candidateInput = some entry) :
    InitialOutputCachedMarkerDisposition root candidateState candidateInput
      rootTargetEvent := by
  cases marker with
  | priorAdversary record member inputEq =>
      exact .priorAdversary record member inputEq
  | freshMarkerTargetEvent event => exact .rootTarget event
  | markerCachedFreshSource markerState markerInput markerAnswer target oldEntry
      found sourceExact outputExact =>
      exact .markerCachedFreshSource markerState markerInput markerAnswer target
        oldEntry found sourceExact outputExact
  | markerCachedProgrammedSource markerState markerInput markerAnswer target
      oldEntry found sourceExact outputExact =>
      exact .markerCachedProgrammedSource markerState markerInput markerAnswer
        target oldEntry found sourceExact outputExact
  | freshAtCandidate rootAbsent candidateAbsent =>
      rw [candidateAbsent] at cached
      contradiction

#print axioms initial_output_fresh_advance_cached_has_fresh_creator
#print axioms output_answer_prefix_advance_key_iff
#print axioms cached_initial_output_refines_exact_marker_disposition

end
end AspisV8Completion.FSV8AlphaInitialCachedCases

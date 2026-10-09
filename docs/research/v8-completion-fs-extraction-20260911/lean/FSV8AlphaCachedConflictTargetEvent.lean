import FSV8AlphaFreshCreatorCoverage
import FSV8MarkerFreshEnumerationSplit
import FSV8ReturnedVerifierFreshTargetEvent

/-!
# Later cached alpha conflicts are charged to the exact root target event

This leaf treats the chronological case used by complete-duplex routing: a
fresh advance has completed one alpha pair, and the next reached pair finds
either its output or advance key in the cache.  Fresh-creator coverage locates
the first fresh record that installed that key.  The preceding advance answer
is a literal prefix of the cached key, so its actual fresh request hits an
operational target at its own request boundary.

The theorem deliberately starts with a *preceding pair*.  A cache conflict in
the first pair has no preceding alpha advance and is not classified by this
result; it remains the separate initial-conflict/restoration branch.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 450000
set_option maxRecDepth 2400

namespace AspisV8Completion.FSV8AlphaCachedConflictTargetEvent

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ProjectedFreshPriorQueryHistory
open AspisK1.V7Tag73SchedulerCausalStateAlignment
open FSAuthenticatedInterleavedPrefixMiddle
open ExtractionCollectorVerifiedSuccessfulReplay
open FSV8V7OracleMachineBridge
open FSV8AlignedAlphaSqueezeStep
open FSV8AlignedAlphaInitialPairDisposition
open FSV8AlphaFreshCreatorCoverage
open FSV8AlphaTableHistoryCoverage
open FSV8AlphaHistoryPhasePrefix
open FSV8CandidateOriginTrace
open FSV8ExactRootCursor
open FSV8ExactRootFunctionalRun
open FSV8MarkerFreshEnumerationSplit
open FSV8MarkerFreshVerifierQueryBridge
open FSV8ReturnedVerifierFreshTargetEvent
open FSV8RootVerifierNativeRequest

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

private theorem answer_prefix_appended_tag
    (answer : Block) (tag : UInt8) :
    HasLiteralStatePrefix answer (List.ofFn answer ++ [tag]) := by
  unfold HasLiteralStatePrefix AspisK1.V7Tag73TranscriptSchedule.bytes
  rw [List.take_append_of_le_length (by simp)]
  simp

/-- A cached initial lookup of the next pair identifies a fresh creator of
that cache entry.  The preceding advance answer is a literal prefix of the
creator input.  If the creator is the preceding advance record itself, this
records the corresponding fixed-point/current-input prefix explicitly. -/
theorem later_cached_pair_has_fresh_creator_prefix
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {v7 : OracleState} {s : Transcript}
    (previous : AlignedSqueezePair tape finiteTape limits v7 s)
    (covered : TableCoveredByFreshHistory previous.afterAdvance)
    (next : AlignedSqueezePair tape finiteTape limits previous.afterAdvance
      (squeeze tape s).2)
    (nextDisposition : InitialPairDisposition tape finiteTape limits
      previous.afterAdvance (squeeze tape s).2 next)
    (cached :
      (∃ outputOrigin advanceOrigin outputMissing entry advanceFound,
        nextDisposition = .outputFreshAdvanceCached outputOrigin advanceOrigin
          outputMissing entry advanceFound) \/
      (∃ outputOrigin entry outputFound,
        nextDisposition = .outputCached outputOrigin entry outputFound)) :
    ∃ creator,
      creator ∈ previous.afterAdvance.history /\
      creator.origin = .fresh /\
      HasLiteralStatePrefix (advanceStep tape s).1 creator.input := by
  rcases cached with advanceCached | outputCached
  · rcases advanceCached with
      ⟨outputOrigin, advanceOrigin, outputMissing, entry, advanceFound,
        dispositionExact⟩
    cases dispositionExact
    obtain ⟨entryInput, entryMember⟩ :=
      lookup_entry_some_input_and_member_local previous.afterAdvance
        (advanceInput (squeeze tape s).2) entry advanceFound
    obtain ⟨creator, creatorMember, creatorFresh, creatorInput,
      _creatorOutput⟩ := covered entry entryMember
    refine ⟨creator, creatorMember, creatorFresh, ?_⟩
    · rw [creatorInput, entryInput]
      change HasLiteralStatePrefix (advanceStep tape s).1
        (List.ofFn (advanceStep tape s).1 ++ [2])
      exact answer_prefix_appended_tag _ _
  · rcases outputCached with
      ⟨outputOrigin, entry, outputFound, dispositionExact⟩
    cases dispositionExact
    obtain ⟨entryInput, entryMember⟩ :=
      lookup_entry_some_input_and_member_local previous.afterAdvance
        (outputInput (squeeze tape s).2) entry outputFound
    obtain ⟨creator, creatorMember, creatorFresh, creatorInput,
      _creatorOutput⟩ := covered entry entryMember
    refine ⟨creator, creatorMember, creatorFresh, ?_⟩
    · rw [creatorInput, entryInput]
      change HasLiteralStatePrefix (advanceStep tape s).1
        (List.ofFn (advanceStep tape s).1 ++ [1])
      exact answer_prefix_appended_tag _ _

/-- Source-shaped exact-root lift for a later cached alpha conflict.  The
history prefixes place the preceding fresh advance at its actual returned
verifier position.  Target membership is constructed from the cached lookup
and its first fresh creator; it is not accepted as a premise. -/
theorem returned_later_cached_alpha_conflict_mem_exact_root_event
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat) (transitionRoom : 2 ≤ transitionFuel)
    (sample : ExactCompilerSample HiddenTape parameters)
    (fallback : Block) (runtime : Runtime TapeIdentity configuration.z)
    (execution : ExactRootFunctionalRun configuration sample.1 sample.2
      fallback runtime)
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {v7 : OracleState} {s : Transcript}
    (previous : AlignedSqueezePair tape finiteTape limits v7 s)
    (advanceFresh : previous.advanceOrigin = .fresh)
    (entryPrefix : execution.prefixes.adversary.finalState.history <+:
      previous.afterOutput.history)
    (finalPrefix : previous.afterAdvance.history <+:
      execution.prefixes.verifier.finalState.history)
    (covered : TableCoveredByFreshHistory previous.afterAdvance)
    (next : AlignedSqueezePair tape finiteTape limits previous.afterAdvance
      (squeeze tape s).2)
    (nextDisposition : InitialPairDisposition tape finiteTape limits
      previous.afterAdvance (squeeze tape s).2 next)
    (cached :
      (∃ outputOrigin advanceOrigin outputMissing entry advanceFound,
        nextDisposition = .outputFreshAdvanceCached outputOrigin advanceOrigin
          outputMissing entry advanceFound) \/
      (∃ outputOrigin entry outputFound,
        nextDisposition = .outputCached outputOrigin entry outputFound)) :
    sample ∈ targetEvent parameters configuration transitionFuel := by
  obtain ⟨creator, creatorMember, creatorFresh, literalPrefix⟩ :=
    later_cached_pair_has_fresh_creator_prefix previous covered next
      nextDisposition cached
  have advanceHistory : previous.afterAdvance.history =
      previous.afterOutput.history ++
        [markerFreshRecord .verifier (advanceInput s)
          (advanceStep tape s).1] := by
    simpa [markerFreshRecord, advanceRecord, advanceInput, advanceFresh,
      AspisK1.V7Tag73TranscriptSchedule.bytes,
      AspisK1.V7Tag73TranscriptSchedule.domAdvance] using
        previous.advanceHistory
  let prior := freshQueryEnumeration
    (historySince execution.prefixes.adversary.finalState
      previous.afterOutput)
  obtain ⟨later, localSplit⟩ := markerFresh_exact_fresh_enumeration_split
    execution.prefixes.adversary.finalState previous.afterOutput
      previous.afterAdvance execution.prefixes.verifier.finalState .verifier
      (advanceInput s) (advanceStep tape s).1 entryPrefix advanceHistory
      finalPrefix
  have enumerationExact :=
    projected_fresh_returned_trace_fresh_query_enumeration_exact
      configuration.verifierLimits .verifier (stagedBudget n m)
      execution.prefixes.adversary.finalState
      (compileScript (wholeStagedScript configuration.firstWork
        configuration.secondWork configuration.z configuration.cuts
        execution.prefixes.adversary.result configuration.initialDigest))
      execution.prefixes.verifier.freshQueries
      execution.prefixes.verifier.result execution.prefixes.verifier.finalState
      execution.prefixes.verifier.steps execution.prefixes.verifier.trace
  have decomposition : execution.prefixes.verifier.freshQueries =
      prior ++ (advanceInput s, (advanceStep tape s).1) :: later := by
    rw [← enumerationExact]
    simpa only [prior, List.append_assoc, List.singleton_append] using localSplit
  obtain ⟨requestState, requestEntryPrefix, priorHistory, sourceRequest⟩ :=
    returned_v8_verifier_query_has_global_native_request parameters
      configuration transitionFuel transitionRoom sample fallback runtime
      execution prior (advanceInput s) (advanceStep tape s).1 later
      decomposition
  apply returned_verifier_fresh_target_hit_mem_exact_root_event parameters
    configuration transitionFuel transitionRoom sample fallback runtime
      execution prior (advanceInput s) (advanceStep tape s).1 later
      decomposition
  intro otherState otherRequest
  have stateExact : otherState = requestState :=
    exact_native_machine_request_state_unique otherRequest sourceRequest
  subst otherState
  rw [advanceHistory] at creatorMember
  rcases List.mem_append.mp creatorMember with priorCreator | currentCreator
  · rcases entryPrefix with ⟨between, priorHistoryExact⟩
    rw [← priorHistoryExact] at priorCreator
    rcases List.mem_append.mp priorCreator with rootCreator | localCreator
    · exact (operational_request_target_hit_iff_mem ∅ requestState.history
        (advanceInput s) (advanceStep tape s).1).mp
          (.priorLiteralPrefix creator
            (requestEntryPrefix.subset rootCreator) literalPrefix)
    · have pairMember : (creator.input, creator.output) ∈
          freshQueryEnumeration
            (historySince execution.prefixes.adversary.finalState
              previous.afterOutput) := by
        unfold historySince
        rw [← priorHistoryExact]
        simp only [List.drop_append_length]
        exact fresh_record_pair_mem_fresh_query_enumeration between creator
          localCreator creatorFresh
      have creatorAtRequest :=
        priorHistory (creator.input, creator.output) pairMember
      exact (operational_request_target_hit_iff_mem ∅ requestState.history
        (advanceInput s) (advanceStep tape s).1).mp
          (.priorLiteralPrefix
            (projectedFreshQueryRecord .verifier
              (creator.input, creator.output))
            creatorAtRequest (by
              simpa [projectedFreshQueryRecord] using literalPrefix))
  · have creatorExact : creator =
        markerFreshRecord .verifier (advanceInput s)
          (advanceStep tape s).1 := by simpa using currentCreator
    subst creator
    exact (operational_request_target_hit_iff_mem ∅ requestState.history
      (advanceInput s) (advanceStep tape s).1).mp
        (.currentLiteralPrefix (by simpa [markerFreshRecord] using literalPrefix))

#print axioms later_cached_pair_has_fresh_creator_prefix
#print axioms returned_later_cached_alpha_conflict_mem_exact_root_event

end
end AspisV8Completion.FSV8AlphaCachedConflictTargetEvent

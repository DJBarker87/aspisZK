import FSV8V7StateAlignment

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8V7CachedAlignment
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open FSV8V7StateAlignment FSV8V7OracleMachineBridge

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape

theorem lookup_none_iff_cache_none {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps}
    {v7 : OracleState} {fs : State Bytes Block}
    (aligned : StateAligned tape finiteTape v7 fs) (input : Bytes) :
    lookupEntry v7 input = none ↔ fs.cache input = none := by
  rw [aligned.cache input]
  cases h : lookupEntry v7 input <;> simp [h]

theorem lookup_some_implies_cache_some {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps}
    {v7 : OracleState} {fs : State Bytes Block}
    (aligned : StateAligned tape finiteTape v7 fs) (input : Bytes)
    (entry : TableEntry) (lookup : lookupEntry v7 input = some entry) :
    fs.cache input = some entry.output := by
  rw [aligned.cache input, lookup]
  rfl

theorem cached_query_output {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps}
    {v7 : OracleState} {fs : State Bytes Block}
    (aligned : StateAligned tape finiteTape v7 fs)
    (input : Bytes) (entry : TableEntry)
    (lookup : lookupEntry v7 input = some entry) :
    (FSOracleExecution.query tape fs input).1 = entry.output := by
  have cache := lookup_some_implies_cache_some aligned input entry lookup
  simp only [FSOracleExecution.query, cache]

def cachedSuccessor (actor : QueryActor) (input : Bytes)
    (entry : TableEntry) (v7 : OracleState) : OracleState :=
  { v7 with
    history := v7.history ++
      [{ input := input, output := entry.output, actor,
         origin := cachedOrigin entry.source }]
    totalCalls := v7.totalCalls + 1 }

theorem cached_successor_aligned {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps}
    {v7 : OracleState} {fs : State Bytes Block}
    (aligned : StateAligned tape finiteTape v7 fs)
    (actor : QueryActor) (input : Bytes) (entry : TableEntry)
    (lookup : lookupEntry v7 input = some entry)
    :
    StateAligned tape finiteTape (cachedSuccessor actor input entry v7)
      (FSOracleExecution.query tape fs input).2 := by
  have cache := lookup_some_implies_cache_some aligned input entry lookup
  have sourceFresh : entry.source = .fresh := by
    have member : entry ∈ v7.table := by
      unfold lookupEntry at lookup
      exact List.mem_of_find?_eq_some lookup
    exact aligned.noProgrammed entry member
  unfold cachedSuccessor
  simp only [FSOracleExecution.query, cache]
  constructor
  · simp [aligned.totalCalls]
  · simpa [aligned.freshCalls]
  · intro other
    simpa [lookupEntry] using aligned.cache other
  · simp [aligned.history, projectRecord, projectOrigin, cachedOrigin,
      sourceFresh]
  · simpa [FSFreshTapeTrace.freshAnswers] using aligned.tapePrefix
  · simpa [NoProgrammed] using aligned.noProgrammed
  · simpa [FreshHistoryCountCoherent, freshAnswerEnumeration, cachedOrigin,
      sourceFresh] using aligned.coherent
  · simpa [FreshHistoryMatchesTape, freshAnswerEnumeration, cachedOrigin,
      sourceFresh] using aligned.tapeMatches
  · simpa [WithinFreshAnswerTape, FreshHistoryCountCoherent,
      freshAnswerEnumeration, cachedOrigin, sourceFresh] using aligned.withinTape
  · exact aligned.tapeCompatibility

#print axioms lookup_none_iff_cache_none
#print axioms lookup_some_implies_cache_some
#print axioms cached_query_output
#print axioms cached_successor_aligned
end AspisV8Completion.FSV8V7CachedAlignment

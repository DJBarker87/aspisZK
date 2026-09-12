import FSV8V7StateAlignment

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8V7CachedAlignment
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open FSV8V7StateAlignment

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

#print axioms lookup_none_iff_cache_none
#print axioms lookup_some_implies_cache_some
#print axioms cached_query_output
end AspisV8Completion.FSV8V7CachedAlignment

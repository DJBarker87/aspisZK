import FSV8V7CachedAlignment

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8V7FreshAlignment
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open FSV8V7StateAlignment FSV8V7CachedAlignment FSV8V7OracleMachineBridge

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape

def freshSuccessor (actor : QueryActor) (input : Bytes) (answer : Block)
    (v7 : OracleState) : OracleState where
  table := v7.table ++ [{ input := input, output := answer, source := .fresh }]
  history := v7.history ++ [{ input := input, output := answer, actor, origin := .fresh }]
  programmingHistory := v7.programmingHistory
  totalCalls := v7.totalCalls + 1
  freshCalls := v7.freshCalls + 1

theorem fresh_controller_answer {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps}
    {v7 : OracleState} {fs : State Bytes Block}
    (aligned : StateAligned tape finiteTape v7 fs)
    (input : Bytes) (available : fs.next < steps) :
    controllerFromFreshAnswerTape finiteTape v7.history input =
      .answer (tape fs.next) := by
  have count : (freshAnswerEnumeration v7.history).length = fs.next := by
    rw [← aligned.freshCalls]
    exact aligned.coherent
  have takeEq := aligned.tapeMatches
  have compat := aligned.tapeCompatibility fs.next available
  unfold controllerFromFreshAnswerTape
  rw [count]
  have hlen : (freshAnswerTapeToList finiteTape).length = steps :=
    fresh_answer_tape_to_list_length _
  simp only [hlen, available, ↓reduceIte]
  rw [compat]
  rfl

theorem fresh_fs_query_output {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps}
    {v7 : OracleState} {fs : State Bytes Block}
    (aligned : StateAligned tape finiteTape v7 fs)
    (input : Bytes) (available : fs.next < steps)
    (lookup : lookupEntry v7 input = none) :
    (FSOracleExecution.query tape fs input).1 = tape fs.next := by
  have cache := (lookup_none_iff_cache_none aligned input).mp lookup
  simp [FSOracleExecution.query, cache]

theorem fresh_query_success_equation {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps}
    {v7 : OracleState} {fs : State Bytes Block}
    (aligned : StateAligned tape finiteTape v7 fs)
    (limits : OracleLimits) (actor : QueryActor) (input : Bytes)
    (available : fs.next < steps)
    (total_ok : v7.totalCalls < limits.totalCalls)
    (fresh_ok : v7.freshCalls < limits.freshCalls)
    (lookup : lookupEntry v7 input = none) :
    queryOracle (controllerFromFreshAnswerTape finiteTape) limits actor v7 input =
      .ok (tape fs.next, freshSuccessor actor input (tape fs.next) v7) := by
  have answer := fresh_controller_answer aligned input available
  simp [queryOracle, Nat.not_le.mpr total_ok, Nat.not_le.mpr fresh_ok, lookup, answer,
    freshSuccessor]

theorem fresh_successor_aligned {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps}
    {v7 : OracleState} {fs : State Bytes Block}
    (aligned : StateAligned tape finiteTape v7 fs)
    (actor : QueryActor) (input : Bytes)
    (available : fs.next < steps)
    (lookup : lookupEntry v7 input = none) :
    StateAligned tape finiteTape (freshSuccessor actor input (tape fs.next) v7)
      (FSOracleExecution.query tape fs input).2 := by
  have cache := (lookup_none_iff_cache_none aligned input).mp lookup
  have answer := fresh_fs_query_output aligned input available lookup
  let limits : OracleLimits :=
    { totalCalls := v7.totalCalls + 1,
      freshCalls := v7.freshCalls + 1,
      programmedPoints := 0 }
  have v7Step :
      queryOracle (controllerFromFreshAnswerTape finiteTape) limits actor v7 input =
        .ok (tape fs.next, freshSuccessor actor input (tape fs.next) v7) :=
    fresh_query_success_equation aligned limits actor input available
      (by simp [limits]) (by simp [limits]) lookup
  unfold freshSuccessor
  simp only [FSOracleExecution.query, cache, answer]
  constructor
  · simp [aligned.totalCalls]
  · simp [aligned.freshCalls]
  · intro other
    change (if other = input then some (tape fs.next) else fs.cache other) = _
    rw [aligned.cache other]
    unfold lookupEntry at lookup ⊢
    rw [List.find?_append]
    by_cases same : other = input
    · subst other; simp [lookup, List.find?]
    · simp [same, Ne.symm same, List.find?]
  · simp [aligned.history, FSV8V7OracleMachineBridge.projectRecord,
      FSV8V7OracleMachineBridge.projectOrigin]
  · dsimp only [State.log, State.next]
    simp only [FSFreshTapeTrace.freshAnswers, List.filterMap_append,
      List.filterMap_cons, List.filterMap_nil, Bool.true_eq, ↓reduceIte,
      List.append_nil]
    change FSFreshTapeTrace.freshAnswers fs.log ++ [tape fs.next] =
      List.map tape (List.range (fs.next + 1))
    rw [List.range_succ, List.map_append, ← aligned.tapePrefix]
    simp
  · intro entry h
    simp only [List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact aligned.noProgrammed entry h
    · rfl
  · exact query_oracle_success_preserves_fresh_history_count
      (controllerFromFreshAnswerTape finiteTape) limits actor v7 _ input _
      aligned.coherent v7Step
  · exact tape_query_success_preserves_fresh_history_contents finiteTape limits actor
      v7 _ input _ aligned.withinTape aligned.tapeMatches
      v7Step
  · exact tape_query_success_preserves_fresh_exposure_bound finiteTape limits actor
      v7 _ input _ aligned.withinTape v7Step
  · exact aligned.tapeCompatibility

#print axioms fresh_controller_answer
#print axioms fresh_fs_query_output
#print axioms fresh_query_success_equation
#print axioms fresh_successor_aligned
end AspisV8Completion.FSV8V7FreshAlignment

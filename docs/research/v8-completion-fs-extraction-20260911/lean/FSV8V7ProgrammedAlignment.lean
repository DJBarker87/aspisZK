import FSV8V7FreshAlignment

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8V7ProgrammedAlignment
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open FSV8V7OracleMachineBridge FSFreshTapeTrace

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape

/- A programmed table entry is already visible in the finite interpreter's
cache.  Its later query is therefore non-fresh, just like a cached fresh
entry; the fresh-only `NoProgrammed` side condition is deliberately absent. -/
structure StateAligned {steps : Nat} (tape : Tape)
    (finiteTape : FreshAnswerTape Block steps)
    (v7 : OracleState) (fs : State Bytes Block) : Prop where
  totalCalls : v7.totalCalls = fs.log.length
  freshCalls : v7.freshCalls = fs.next
  cache : ∀ input, fs.cache input = (lookupEntry v7 input).map TableEntry.output
  history : fs.log = v7.history.map projectRecord
  tapePrefix : freshAnswers fs.log = (List.range fs.next).map tape
  coherent : FreshHistoryCountCoherent v7
  tapeMatches : FreshHistoryMatchesTape finiteTape v7
  withinTape : WithinFreshAnswerTape finiteTape v7
  tapeCompatibility : ∀ i (h : i < steps),
    tape i = (freshAnswerTapeToList finiteTape).get
      ⟨i, by simpa using h⟩

theorem empty_aligned {steps : Nat} (tape : Tape)
    (finiteTape : FreshAnswerTape Block steps)
    (compatibility : ∀ i (h : i < steps),
      tape i = (freshAnswerTapeToList finiteTape).get
        ⟨i, by simpa using h⟩) :
    StateAligned tape finiteTape emptyOracle
      (FSFirstFresh.empty : State Bytes Block) := by
  constructor
  · rfl
  · rfl
  · intro input; rfl
  · rfl
  · rfl
  · exact empty_oracle_fresh_history_count_coherent
  · exact empty_oracle_fresh_history_matches_tape finiteTape
  · exact empty_oracle_within_fresh_answer_tape finiteTape
  · exact compatibility

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

def cachedSuccessor (actor : QueryActor) (input : Bytes)
    (entry : TableEntry) (v7 : OracleState) : OracleState :=
  { v7 with
    history := v7.history ++
      [{ input := input, output := entry.output, actor,
         origin := cachedOrigin entry.source }]
    totalCalls := v7.totalCalls + 1 }

theorem cached_query_success_equation
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (input : Bytes) (entry : TableEntry)
    (v7 : OracleState) (total_ok : v7.totalCalls < limits.totalCalls)
    (lookup : lookupEntry v7 input = some entry) :
    queryOracle controller limits actor v7 input =
      .ok (entry.output, cachedSuccessor actor input entry v7) := by
  simp [queryOracle, Nat.not_le.mpr total_ok, lookup, cachedSuccessor]

theorem cached_successor_aligned {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps}
    {v7 : OracleState} {fs : State Bytes Block}
    (aligned : StateAligned tape finiteTape v7 fs)
    (actor : QueryActor) (input : Bytes) (entry : TableEntry)
    (lookup : lookupEntry v7 input = some entry) :
    StateAligned tape finiteTape (cachedSuccessor actor input entry v7)
      (FSOracleExecution.query tape fs input).2 := by
  have cache := lookup_some_implies_cache_some aligned input entry lookup
  unfold cachedSuccessor
  simp only [FSOracleExecution.query, cache]
  constructor
  · simp [aligned.totalCalls]
  · simpa [aligned.freshCalls]
  · intro other
    simpa [lookupEntry] using aligned.cache other
  · cases entry.source <;>
      simp [aligned.history, projectRecord, projectOrigin, cachedOrigin]
  · simpa [FSFreshTapeTrace.freshAnswers] using aligned.tapePrefix
  · cases entry.source <;>
      simpa [FreshHistoryCountCoherent, freshAnswerEnumeration, cachedOrigin] using
        aligned.coherent
  · cases entry.source <;>
      simpa [FreshHistoryMatchesTape, freshAnswerEnumeration, cachedOrigin] using
        aligned.tapeMatches
  · cases entry.source <;>
      simpa [WithinFreshAnswerTape, FreshHistoryCountCoherent,
        freshAnswerEnumeration, cachedOrigin] using aligned.withinTape
  · exact aligned.tapeCompatibility

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
  simp [queryOracle, Nat.not_le.mpr total_ok, Nat.not_le.mpr fresh_ok, lookup,
    answer, freshSuccessor]

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
  let stepLimits : OracleLimits :=
    { totalCalls := v7.totalCalls + 1
      freshCalls := v7.freshCalls + 1
      programmedPoints := v7.programmingHistory.length }
  have v7Step :
      queryOracle (controllerFromFreshAnswerTape finiteTape) stepLimits actor v7 input =
        .ok (tape fs.next, freshSuccessor actor input (tape fs.next) v7) :=
    fresh_query_success_equation aligned stepLimits actor input available
      (by simp [stepLimits]) (by simp [stepLimits]) lookup
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
  · simp [aligned.history, projectRecord, projectOrigin]
  · dsimp only [State.log, State.next]
    simp only [FSFreshTapeTrace.freshAnswers, List.filterMap_append,
      List.filterMap_cons, List.filterMap_nil, Bool.true_eq, ↓reduceIte,
      List.append_nil]
    change FSFreshTapeTrace.freshAnswers fs.log ++ [tape fs.next] =
      List.map tape (List.range (fs.next + 1))
    rw [List.range_succ, List.map_append, ← aligned.tapePrefix]
    simp
  · exact query_oracle_success_preserves_fresh_history_count
      (controllerFromFreshAnswerTape finiteTape) stepLimits
      actor v7 _ input _ aligned.coherent v7Step
  · exact tape_query_success_preserves_fresh_history_contents finiteTape
      stepLimits actor v7 _ input _ aligned.withinTape aligned.tapeMatches v7Step
  · exact tape_query_success_preserves_fresh_exposure_bound finiteTape
      stepLimits actor v7 _ input _ aligned.withinTape v7Step
  · exact aligned.tapeCompatibility

/-- Exact visible result correspondence. -/
def ResultAligned {A : Type} : Option A → MachineHalt A → Prop
  | some value, halt => halt = .returned value
  | none, halt => halt = .oracleAbort .controllerRefused

theorem run_compileScript_aligned {A : Type} {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps}
    (limits : OracleLimits) (actor : QueryActor) :
    forall {n : Nat} (script : Script Bytes Block A n)
      (v7 : OracleState) (fs : State Bytes Block),
      StateAligned tape finiteTape v7 fs ->
      v7.totalCalls + n <= limits.totalCalls ->
      v7.freshCalls + n <= limits.freshCalls ->
      fs.next + n <= steps ->
      let machine := runMachine (controllerFromFreshAnswerTape finiteTape)
        limits actor n v7 (compileScript script)
      ResultAligned (run tape script fs).1 machine.halt /\
        StateAligned tape finiteTape machine.oracle (run tape script fs).2 := by
  intro n script
  induction script with
  | done value =>
      intro v7 fs aligned totalRoom freshRoom tapeRoom
      constructor
      · simp [ResultAligned, FSOracleExecution.run,
          compileScript, runMachine]
      · simpa [FSOracleExecution.run, compileScript, runMachine] using aligned
  | abort =>
      intro v7 fs aligned totalRoom freshRoom tapeRoom
      constructor
      · simp [ResultAligned, FSOracleExecution.run,
          compileScript, runMachine]
      · simpa [FSOracleExecution.run, compileScript, runMachine] using aligned
  | @ask remaining input next ih =>
      intro v7 fs aligned totalRoom freshRoom tapeRoom
      have totalNow : v7.totalCalls < limits.totalCalls := by omega
      have tapeNow : fs.next < steps := by omega
      cases lookup : lookupEntry v7 input with
      | some entry =>
        let v7Next := cachedSuccessor actor input entry v7
        let fsNext := (FSOracleExecution.query tape fs input).2
        have queryEq := cached_query_success_equation
          (controllerFromFreshAnswerTape finiteTape) limits actor input entry v7
          totalNow lookup
        have alignedNext := cached_successor_aligned aligned actor input entry lookup
        have totalNext : v7Next.totalCalls + remaining <= limits.totalCalls := by
          simp [v7Next, cachedSuccessor]; omega
        have freshNext : v7Next.freshCalls + remaining <= limits.freshCalls := by
          simp [v7Next, cachedSuccessor]; omega
        have tapeNext : fsNext.next + remaining <= steps := by
          have cache := lookup_some_implies_cache_some aligned input entry lookup
          simp [fsNext, FSOracleExecution.query, cache]; omega
        have answerEq : (FSOracleExecution.query tape fs input).1 = entry.output := by
          simp [FSOracleExecution.query, lookup_some_implies_cache_some aligned input entry lookup]
        have inductiveStep := ih entry.output v7Next fsNext alignedNext
          totalNext freshNext tapeNext
        simpa [compileScript, runMachine, queryEq, FSOracleExecution.run, answerEq,
          v7Next, fsNext] using inductiveStep
      | none =>
        let answer := tape fs.next
        let v7Next := freshSuccessor actor input answer v7
        let fsNext := (FSOracleExecution.query tape fs input).2
        have freshNow : v7.freshCalls < limits.freshCalls := by omega
        have queryEq := fresh_query_success_equation aligned limits actor input
          tapeNow totalNow freshNow lookup
        have alignedNext := fresh_successor_aligned aligned actor input tapeNow lookup
        have totalNext : v7Next.totalCalls + remaining <= limits.totalCalls := by
          simp [v7Next, freshSuccessor]; omega
        have freshNext : v7Next.freshCalls + remaining <= limits.freshCalls := by
          simp [v7Next, freshSuccessor]; omega
        have tapeNext : fsNext.next + remaining <= steps := by
          have cache := (lookup_none_iff_cache_none aligned input).mp lookup
          simp [fsNext, FSOracleExecution.query, cache]; omega
        have answerEq := fresh_fs_query_output aligned input tapeNow lookup
        have inductiveStep := ih answer v7Next fsNext alignedNext
          totalNext freshNext tapeNext
        simpa [compileScript, runMachine, queryEq, FSOracleExecution.run, answerEq,
          answer, v7Next, fsNext] using inductiveStep

#print axioms cached_successor_aligned
#print axioms fresh_successor_aligned
#print axioms run_compileScript_aligned
end AspisV8Completion.FSV8V7ProgrammedAlignment

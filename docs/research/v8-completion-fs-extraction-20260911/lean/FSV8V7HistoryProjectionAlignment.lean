import FSV8V7FreshAlignment
import FSV8V7WholeScriptUniformLaw

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8V7HistoryProjectionAlignment
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open FSV8V7OracleMachineBridge FSV8V7StateAlignment
open FSV8V7WholeScriptUniformLaw

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape

theorem projected_fresh_answers_eq_enumeration :
    ∀ history : List QueryRecord,
      FSFreshTapeTrace.freshAnswers (history.map projectRecord) =
        freshAnswerEnumeration history := by
  intro history
  induction history with
  | nil => rfl
  | cons record rest ih =>
      cases record with
      | mk input output actor origin =>
          have ih' :
              List.filterMap
                  (fun x => if (projectRecord x).fresh = true then
                    some (projectRecord x).answer else none) rest =
                freshAnswerEnumeration rest := by
            simpa [FSFreshTapeTrace.freshAnswers] using ih
          cases origin with
          | fresh =>
              change output :: FSFreshTapeTrace.freshAnswers
                  (List.map projectRecord rest) = output :: freshAnswerEnumeration rest
              exact congrArg (List.cons output) ih
          | programmed =>
              change FSFreshTapeTrace.freshAnswers
                  (List.map projectRecord rest) = freshAnswerEnumeration rest
              exact ih
          | cached =>
              change FSFreshTapeTrace.freshAnswers
                  (List.map projectRecord rest) = freshAnswerEnumeration rest
              exact ih

/-! These are the source-shaped facts needed to view a V7 fresh-only
prehistory as the current FS state.  The cache and log projection themselves
are constructed by `projectOracleState`; they are not supplied as premises. -/
structure FreshOnlyProjectionFacts {steps : Nat} (tape : Tape)
    (finiteTape : FreshAnswerTape Block steps) (v7 : OracleState) : Prop where
  historyTotal : v7.history.length = v7.totalCalls
  noProgrammed : NoProgrammed v7
  freshCount : FreshHistoryCountCoherent v7
  tapeMatches : FreshHistoryMatchesTape finiteTape v7
  withinTape : WithinFreshAnswerTape finiteTape v7
  tapePrefix :
    FSFreshTapeTrace.freshAnswers (v7.history.map projectRecord) =
      (List.range v7.freshCalls).map tape
  tapeCompatibility : ∀ i (h : i < steps),
    tape i = (freshAnswerTapeToList finiteTape).get
      ⟨i, by simpa using h⟩

theorem project_state_aligned {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps} {v7 : OracleState}
    (facts : FreshOnlyProjectionFacts tape finiteTape v7) :
    StateAligned tape finiteTape v7 (projectOracleState v7) := by
  constructor
  · unfold projectOracleState
    simpa using facts.historyTotal.symm
  · rfl
  · intro input
    rfl
  · rfl
  · simpa [projectOracleState] using facts.tapePrefix
  · exact facts.noProgrammed
  · exact facts.freshCount
  · exact facts.tapeMatches
  · exact facts.withinTape
  · exact facts.tapeCompatibility

theorem query_success_preserves_no_programmed
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : OracleState)
    (input : Bytes) (output : Block)
    (noProgrammed : NoProgrammed state)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState)) :
    NoProgrammed nextState := by
  unfold queryOracle at success
  split at success <;> try contradiction
  next _ =>
    split at success
    next entry _ =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨_, rfl⟩
      intro entry' membership
      simpa using noProgrammed entry' membership
    next _ =>
      split at success <;> try contradiction
      next _ =>
        split at success <;> try contradiction
        next answer answered =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at success
          rcases success with ⟨_, rfl⟩
          intro entry' membership
          simp only [List.mem_append, List.mem_singleton] at membership
          rcases membership with old | fresh
          · exact noProgrammed entry' old
          · subst entry'
            rfl

theorem run_machine_preserves_no_programmed
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) (noProgrammed : NoProgrammed state) :
    NoProgrammed
      (runMachine controller limits actor fuel state program).oracle := by
  induction fuel generalizing state program with
  | zero => cases program <;> simpa [runMachine] using noProgrammed
  | succ fuel ih =>
      cases program with
      | pure result => simpa [runMachine] using noProgrammed
      | abort reason => simpa [runMachine] using noProgrammed
      | query input next =>
          simp only [runMachine]
          cases queried : queryOracle controller limits actor state input with
          | error reason => simpa using noProgrammed
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              have nextNoProgrammed := query_success_preserves_no_programmed
                controller limits actor state nextState input output noProgrammed queried
              simpa using ih nextState (next output) nextNoProgrammed

theorem query_success_preserves_history_total
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : OracleState)
    (input : Bytes) (output : Block)
    (historyTotal : state.history.length = state.totalCalls)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState)) :
    nextState.history.length = nextState.totalCalls := by
  unfold queryOracle at success
  split at success <;> try contradiction
  next _ =>
    split at success
    next entry _ =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨_, rfl⟩
      simp [historyTotal]
    next _ =>
      split at success <;> try contradiction
      next _ =>
        split at success <;> try contradiction
        next answer answered =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at success
          rcases success with ⟨_, rfl⟩
          simp [historyTotal]

theorem run_machine_preserves_history_total
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result)
    (historyTotal : state.history.length = state.totalCalls) :
    (runMachine controller limits actor fuel state program).oracle.history.length =
      (runMachine controller limits actor fuel state program).oracle.totalCalls := by
  induction fuel generalizing state program with
  | zero => cases program <;> simpa [runMachine] using historyTotal
  | succ fuel ih =>
      cases program with
      | pure result => simpa [runMachine] using historyTotal
      | abort reason => simpa [runMachine] using historyTotal
      | query input next =>
          simp only [runMachine]
          cases queried : queryOracle controller limits actor state input with
          | error reason => simpa using historyTotal
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              have nextHistoryTotal := query_success_preserves_history_total
                controller limits actor state nextState input output historyTotal queried
              simpa using ih nextState (next output) nextHistoryTotal

theorem uniform_run_fresh_only_projection_facts
    {Result : Type*} {steps : Nat} (tape : Tape)
    (finiteTape : FreshAnswerTape Block steps) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (program : OracleMachine Result)
    (compatibility : ∀ i (h : i < steps),
      tape i = (freshAnswerTapeToList finiteTape).get
        ⟨i, by simpa using h⟩)
    (projectedPrefix :
      FSFreshTapeTrace.freshAnswers
          ((runMachineFromUniformFreshTape steps limits actor fuel program
            finiteTape).oracle.history.map projectRecord) =
        (List.range
          (runMachineFromUniformFreshTape steps limits actor fuel program
            finiteTape).oracle.freshCalls).map tape) :
    FreshOnlyProjectionFacts tape finiteTape
      ((runMachineFromUniformFreshTape steps limits actor fuel program finiteTape).oracle) := by
  let final := runMachineFromUniformFreshTape steps limits actor fuel program finiteTape
  have total := run_machine_preserves_history_total
    (controllerFromFreshAnswerTape finiteTape) limits actor fuel emptyOracle
    program (by rfl)
  have noProgrammed := run_machine_preserves_no_programmed
    (controllerFromFreshAnswerTape finiteTape) limits actor fuel emptyOracle
    program (by simp [NoProgrammed, emptyOracle])
  have within := uniform_tape_machine_fresh_exposure_bound
    steps limits actor fuel program finiteTape
  have content := uniform_tape_machine_fresh_answers_are_consumed_prefix
    steps limits actor fuel program finiteTape
  refine ⟨?_, noProgrammed, within.1, content, within, projectedPrefix, compatibility⟩
  simpa [runMachineFromUniformFreshTape, final] using total

theorem extended_tape_projected_prefix
    {steps : Nat} (tape : FreshAnswerTape Block steps) (fallback : Block)
    (n : Nat) (bounded : n ≤ steps) :
      (freshAnswerTapeToList tape).take n =
      (List.range n).map (extendFreshTape tape fallback) := by
  apply List.ext_getElem
  · simp [List.length_take, Nat.min_eq_left bounded]
  · intro i leftBound rightBound
    have iN : i < n := by
      simpa [List.length_take, Nat.min_eq_left bounded] using leftBound
    have iBound : i < steps := lt_of_lt_of_le iN bounded
    simp only [List.getElem_take, List.getElem_map, List.getElem_range]
    exact (extendFreshTape_compatible tape fallback i iBound).symm

theorem uniform_run_extended_fresh_only_projection_facts
    {Result : Type*} {steps : Nat} (finiteTape : FreshAnswerTape Block steps)
    (fallback : Block) (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (program : OracleMachine Result) :
    FreshOnlyProjectionFacts (extendFreshTape finiteTape fallback) finiteTape
      (runMachineFromUniformFreshTape steps limits actor fuel program finiteTape).oracle := by
  let final := runMachineFromUniformFreshTape steps limits actor fuel program finiteTape
  have within := uniform_tape_machine_fresh_exposure_bound
    steps limits actor fuel program finiteTape
  have content := uniform_tape_machine_fresh_answers_are_consumed_prefix
    steps limits actor fuel program finiteTape
  have projected := projected_fresh_answers_eq_enumeration final.oracle.history
  have prefixProof :
      FSFreshTapeTrace.freshAnswers (final.oracle.history.map projectRecord) =
        (List.range final.oracle.freshCalls).map
          (extendFreshTape finiteTape fallback) := by
    rw [projected, content, extended_tape_projected_prefix finiteTape fallback
      final.oracle.freshCalls within.2]
  exact uniform_run_fresh_only_projection_facts
    (extendFreshTape finiteTape fallback) finiteTape limits actor fuel program
    (extendFreshTape_compatible finiteTape fallback) prefixProof

theorem uniform_run_projected_state_aligned_of_prefix
    {Result : Type*} {steps : Nat} (tape : Tape)
    (finiteTape : FreshAnswerTape Block steps) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (program : OracleMachine Result)
    (compatibility : ∀ i (h : i < steps),
      tape i = (freshAnswerTapeToList finiteTape).get
        ⟨i, by simpa using h⟩)
    (projectedPrefix :
      FSFreshTapeTrace.freshAnswers
          ((runMachineFromUniformFreshTape steps limits actor fuel program
            finiteTape).oracle.history.map projectRecord) =
        (List.range
          (runMachineFromUniformFreshTape steps limits actor fuel program
            finiteTape).oracle.freshCalls).map tape) :
    StateAligned tape finiteTape
      (runMachineFromUniformFreshTape steps limits actor fuel program finiteTape).oracle
      (projectOracleState
        (runMachineFromUniformFreshTape steps limits actor fuel program finiteTape).oracle) :=
  project_state_aligned
    (uniform_run_fresh_only_projection_facts tape finiteTape limits actor fuel program
      compatibility projectedPrefix)

theorem uniform_run_projected_state_aligned
    {Result : Type*} {steps : Nat} (finiteTape : FreshAnswerTape Block steps)
    (fallback : Block) (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (program : OracleMachine Result) :
    StateAligned (extendFreshTape finiteTape fallback) finiteTape
      (runMachineFromUniformFreshTape steps limits actor fuel program finiteTape).oracle
      (projectOracleState
        (runMachineFromUniformFreshTape steps limits actor fuel program finiteTape).oracle) :=
  project_state_aligned
    (uniform_run_extended_fresh_only_projection_facts finiteTape fallback limits actor
      fuel program)

#print axioms project_state_aligned
#print axioms query_success_preserves_no_programmed
#print axioms run_machine_preserves_no_programmed
#print axioms query_success_preserves_history_total
#print axioms run_machine_preserves_history_total
#print axioms uniform_run_fresh_only_projection_facts
#print axioms uniform_run_projected_state_aligned
end AspisV8Completion.FSV8V7HistoryProjectionAlignment

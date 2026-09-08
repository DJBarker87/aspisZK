import AspisFormal.K1.V7Tag73RootSqueezePreparationClosure
import AspisFormal.K1.V7Tag73PreparedRestorationRoles
import AspisFormal.K1.V7Tag73OracleTableProvenance
import AspisFormal.K1.V7Tag73PrefixTableProvenance
import AspisFormal.K1.V7Tag73NoPairOccurrenceTrichotomy
import AspisFormal.K1.V7Tag73CumulativeReplayHistory
import AspisFormal.K1.V7Tag73NoPairReplay
import AspisFormal.K1.V7Tag73ExactCompilerTargetClean

/-!
# Root squeeze preparation reaches the real fork cursor

The root-sweep client already requests every deployed transition.  The prior
module proves that a literal paired squeeze always prepares successfully,
including adversary-first prequeries.  This module discharges the remaining
deterministic dispatcher guard that is semantic rather than a resource bound:
the prepared prefix is history/total-call coherent.  With the two explicit
global resource inequalities, the real dispatcher therefore emits its
literal pair-fork cursor.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73RootSqueezeForkEmission

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73CompletedFullRunProjection
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalNodeCertificate
open AspisK1.V7Tag73OracleTableProvenance
open AspisK1.V7Tag73PrefixTableProvenance
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73NoPairReplay
open AspisK1.V7Tag73CumulativeReplayHistory
open AspisK1.V7Tag73ExactCompilerTargetClean
open AspisK1.V7Tag73PreparedRestorationRoles
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawStrictReplacementSuffix
open AspisK1.V7Tag73RootSqueezePreparationClosure
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SequentialOracleRuns
open AspisK1.V7Tag73TotalizedMachineReflection
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73UniformRawVerifierExecution

noncomputable section

universe u

private theorem first_either_none_of_query_answer_trace_eq_root
    (outputInput advanceInput : ShaInput)
    (actual expected : List QueryRecord)
    (traceExact : queryAnswerTrace actual = queryAnswerTrace expected)
    (expectedNone :
      firstEitherInputOccurrence outputInput advanceInput expected = none) :
    firstEitherInputOccurrence outputInput advanceInput actual = none := by
  apply (first_either_input_occurrence_none_iff outputInput advanceInput
    actual).mpr
  intro record recordMember
  have projectedMember : (record.input, record.output) ∈
      queryAnswerTrace actual := List.mem_map.mpr ⟨record, recordMember, rfl⟩
  rw [traceExact] at projectedMember
  rcases List.mem_map.mp projectedMember with
    ⟨expectedRecord, expectedMember, pairExact⟩
  have expectedFresh := (first_either_input_occurrence_none_iff outputInput
    advanceInput expected).mp expectedNone expectedRecord expectedMember
  have inputExact : expectedRecord.input = record.input :=
    congrArg Prod.fst pairExact
  exact ⟨fun equal => expectedFresh.1 (inputExact.trans equal),
    fun equal => expectedFresh.2 (inputExact.trans equal)⟩

/-- In a provenance-covered oracle with no earlier programming, absence of
both pair inputs from the query history is literal lookup absence. -/
theorem pair_lookups_none_of_query_absent_and_programming_empty
    (state : OracleState) (outputInput advanceInput : ShaInput)
    (covered : TableCoveredByQueryOrProgramming state)
    (queryAbsent : firstEitherInputOccurrence outputInput advanceInput
      state.history = none)
    (programmingEmpty : state.programmingHistory = []) :
    lookupEntry state outputInput = none ∧
      lookupEntry state advanceInput = none := by
  constructor
  · cases found : lookupEntry state outputInput with
    | none => rfl
    | some entry =>
        obtain ⟨record, member, _inputExact, _outputExact⟩ :=
          no_pair_output_lookup_conflict_is_prior_programming state
            outputInput advanceInput entry covered queryAbsent found
        rw [programmingEmpty] at member
        simp at member
  · cases found : lookupEntry state advanceInput with
    | none => rfl
    | some entry =>
        obtain ⟨record, member, _inputExact, _outputExact⟩ :=
          no_pair_advance_lookup_conflict_is_prior_programming state
            outputInput advanceInput entry covered queryAbsent found
        rw [programmingEmpty] at member
        simp at member

/-- With an empty programming ledger and room for two points, literal lookup
freshness makes pair programming total for every two scheduler outputs. -/
theorem program_concrete_pair_succeeds_from_empty_ledger
    (limits : OracleLimits) (order : PairProgrammingOrder)
    (state : OracleState) (outputInput advanceInput : ShaInput)
    (forkOutput forkAdvance : Digest256)
    (distinct : outputInput ≠ advanceInput)
    (outputMissing : lookupEntry state outputInput = none)
    (advanceMissing : lookupEntry state advanceInput = none)
    (programmingEmpty : state.programmingHistory = [])
    (programmingRoom : 2 ≤ limits.programmedPoints) :
    ∃ afterBoth,
      programConcretePair limits order state outputInput advanceInput
        forkOutput forkAdvance = .ready afterBoth := by
  cases order with
  | outputThenAdvance =>
      let outputPoint : Programming :=
        { input := outputInput, output := forkOutput }
      let afterOutput :=
        appendProgrammedPoint .extractorReplay state outputPoint
      have outputWithin : state.programmingHistory.length <
          limits.programmedPoints := by
        simp [programmingEmpty]
        omega
      have outputExact : programConcreteHalf limits state outputInput
          forkOutput = .ok afterOutput := by
        exact program_oracle_fresh_point_exact limits .extractorReplay state
          outputPoint outputWithin outputMissing
      have advanceStillMissing : lookupEntry afterOutput advanceInput = none := by
        exact append_programmed_point_other_input_remains_missing
          .extractorReplay state outputPoint advanceInput advanceMissing distinct
      have advanceWithin : afterOutput.programmingHistory.length <
          limits.programmedPoints := by
        simp [afterOutput, appendProgrammedPoint, programmingEmpty]
        omega
      let advancePoint : Programming :=
        { input := advanceInput, output := forkAdvance }
      let afterBoth :=
        appendProgrammedPoint .extractorReplay afterOutput advancePoint
      have advanceExact : programConcreteHalf limits afterOutput advanceInput
          forkAdvance = .ok afterBoth := by
        exact program_oracle_fresh_point_exact limits .extractorReplay
          afterOutput advancePoint advanceWithin advanceStillMissing
      refine ⟨afterBoth, ?_⟩
      simp only [programConcretePair, distinct, ↓reduceIte, outputMissing,
        Option.isSome_none, advanceMissing]
      simp only [Bool.false_eq_true, if_false]
      simp only [outputExact]
      rw [advanceExact]
  | advanceThenOutput =>
      let advancePoint : Programming :=
        { input := advanceInput, output := forkAdvance }
      let afterAdvance :=
        appendProgrammedPoint .extractorReplay state advancePoint
      have advanceWithin : state.programmingHistory.length <
          limits.programmedPoints := by
        simp [programmingEmpty]
        omega
      have advanceExact : programConcreteHalf limits state advanceInput
          forkAdvance = .ok afterAdvance := by
        exact program_oracle_fresh_point_exact limits .extractorReplay state
          advancePoint advanceWithin advanceMissing
      have outputStillMissing : lookupEntry afterAdvance outputInput = none := by
        exact append_programmed_point_other_input_remains_missing
          .extractorReplay state advancePoint outputInput outputMissing
            distinct.symm
      have outputWithin : afterAdvance.programmingHistory.length <
          limits.programmedPoints := by
        simp [afterAdvance, appendProgrammedPoint, programmingEmpty]
        omega
      let outputPoint : Programming :=
        { input := outputInput, output := forkOutput }
      let afterBoth :=
        appendProgrammedPoint .extractorReplay afterAdvance outputPoint
      have outputExact : programConcreteHalf limits afterAdvance outputInput
          forkOutput = .ok afterBoth := by
        exact program_oracle_fresh_point_exact limits .extractorReplay
          afterAdvance outputPoint outputWithin outputStillMissing
      refine ⟨afterBoth, ?_⟩
      simp only [programConcretePair, distinct, ↓reduceIte, outputMissing,
        Option.isSome_none, advanceMissing]
      simp only [Bool.false_eq_true, if_false]
      simp only [advanceExact]
      rw [outputExact]

theorem successful_query_preserves_history_total_coherent
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : OracleState)
    (input : ShaInput) (output : ShaOutput)
    (coherent : HistoryTotalCoherent state)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState)) :
    HistoryTotalCoherent nextState := by
  obtain ⟨record, historyExact, _actorExact⟩ :=
    query_oracle_success_appends_actor_record controller limits actor state
      nextState input output success
  have counterExact :=
    (query_oracle_success_counter_step controller limits actor state nextState
      input output success).1
  unfold HistoryTotalCoherent at coherent ⊢
  rw [historyExact, counterExact]
  simp only [List.length_append, List.length_singleton]
  omega

theorem run_prefix_preserves_history_total_coherent
    {Result : Type*}
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result)
    (coherent : HistoryTotalCoherent state) :
    HistoryTotalCoherent
      (runPrefix controller limits actor fuel state program).oracle := by
  induction fuel generalizing state program with
  | zero => simpa [runPrefix] using coherent
  | succ fuel inductionHypothesis =>
      cases program with
      | pure result => simpa [runPrefix] using coherent
      | abort reason => simpa [runPrefix] using coherent
      | query input next =>
          cases queried : queryOracle controller limits actor state input with
          | error reason => simpa [runPrefix, queried] using coherent
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              have nextCoherent :=
                successful_query_preserves_history_total_coherent controller
                  limits actor state nextState input output coherent queried
              simpa [runPrefix, queried] using
                inductionHypothesis nextState (next output) nextCoherent

theorem run_machine_preserves_history_total_coherent
    {Result : Type*}
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result)
    (coherent : HistoryTotalCoherent state) :
    HistoryTotalCoherent
      (runMachine controller limits actor fuel state program).oracle := by
  induction fuel generalizing state program with
  | zero =>
      cases program <;> simpa [runMachine] using coherent
  | succ fuel inductionHypothesis =>
      cases program with
      | pure result => simpa [runMachine] using coherent
      | abort reason => simpa [runMachine] using coherent
      | query input next =>
          cases queried : queryOracle controller limits actor state input with
          | error reason => simpa [runMachine, queried] using coherent
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              have nextCoherent :=
                successful_query_preserves_history_total_coherent controller
                  limits actor state nextState input output coherent queried
              simpa [runMachine, queried] using
                inductionHypothesis nextState (next output) nextCoherent

/-- Observe only the first, output-answer phase of a restoration pair fork.
Unlike the legacy header observer, this deliberately rejects `.forkAdvance`,
so the resulting theorem is usable by a pre-answer alpha-output router. -/
def schedulerNativePairForkHeader?
    {globalOracleCalls : Nat} {Result : Type*}
    (cursor : SchedulerNativeCursor globalOracleCalls Result) :
    Option PreparedForkHeader :=
  match cursor with
  | .forkPair frozenHistory _pairRoom outputInput advanceInput template _next =>
      some { frozenHistory, outputInput, advanceInput, template }
  | .machine .. | .forkAdvance .. | .returned .. | .failed .. => none

/-- The guarded prepared dispatcher starts at `.forkPair`, not midway through
the answer-dependent `.forkAdvance` phase. -/
theorem dispatch_prepared_restoration_emits_pair_fork_header
    {Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (prepared : PreparedConcreteRestoration Statement Proof Payload)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (resume : ConcreteRestorationReply →
      ConcreteRestorationAccumulator Statement Proof Payload →
        SchedulerNativeCursor globalOracleCalls
          (ConcreteRestorationClientRun Statement Proof Payload Result))
    (prefixCoherent : HistoryTotalCoherent prepared.programmingBase)
    (globalLimit : configuration.oracleLimits.totalCalls ≤ globalOracleCalls)
    (pairRoom : prepared.programmingBase.history.length + 2 ≤
      globalOracleCalls) :
    schedulerNativePairForkHeader?
        (dispatchPreparedRestoration startProgram environment configuration
          prepared accumulator resume) =
      some (preparedForkHeader configuration prepared) := by
  unfold dispatchPreparedRestoration
  rw [dif_pos prefixCoherent, dif_pos globalLimit, dif_pos pairRoom]
  rfl

/-- A literal root squeeze prepares successfully in every live accumulator
that still stores the completed root at index zero.  Its programming base is
coherent: either the completed root oracle itself or a literal prefix replay
from `emptyOracle`. -/
theorem literal_root_squeeze_request_prepares_ready_coherent
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type u}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (runs : RootProjectedTotalizedRuns machine hidden runtime)
    (configuration : ConcreteRestorationConfiguration)
    (limitsExact : configuration.oracleLimits = machine.adversaryLimits)
    (transitionIndex : Nat)
    (transition : FutureFreeTransition)
    (transitionExact : verifierTransitionAt? runtime.node transitionIndex =
      some transition)
    (outputInput advanceInput : ShaInput)
    (pairExact : squeezePairInputsOfTransition transition =
      some (outputInput, advanceInput))
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (rootStored : accumulator.node? 0 = some runtime.node) :
    ∃ prepared : PreparedConcreteRestoration Statement Proof Payload,
      prepareConcreteRestorationFromStartProgram
          (machine.blackBox.start hidden machine.observation) configuration
          accumulator
          { nodeId := 0, verifierTransitionIndex := transitionIndex } =
        .ready prepared ∧
      HistoryTotalCoherent prepared.programmingBase ∧
      firstEitherInputOccurrence prepared.outputInput prepared.advanceInput
          prepared.programmingBase.history = none ∧
      prepared.programmingBase.programmingHistory = [] ∧
      TableCoveredByQueryOrProgramming prepared.programmingBase := by
  rcases runs with ⟨adversarySteps, _verifierSteps, adversaryRun,
    _verifierRun⟩
  have returnedRun := run_machine_totalized_ok_reflects
    (rootAdversaryProjectedController runtime) machine.adversaryLimits
    .adversary machine.adversaryFuel emptyOracle
    (machine.blackBox.start hidden machine.observation)
    runtime.adversaryValue runtime.proverFinalOracle adversarySteps adversaryRun
  have rootFinalCoherent : HistoryTotalCoherent runtime.proverFinalOracle := by
    have returnedOracle :
        (runMachine (rootAdversaryProjectedController runtime)
          machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
          (machine.blackBox.start hidden machine.observation)).oracle =
            runtime.proverFinalOracle :=
      congrArg MachineRun.oracle returnedRun
    rw [← returnedOracle]
    exact run_machine_preserves_history_total_coherent
      (rootAdversaryProjectedController runtime) machine.adversaryLimits
      .adversary machine.adversaryFuel emptyOracle
      (machine.blackBox.start hidden machine.observation)
      empty_oracle_history_total_coherent
  have rootFinalProgrammingEmpty :
      runtime.proverFinalOracle.programmingHistory = [] := by
    have preserved := run_machine_preserves_cumulative_programming_history
      (rootAdversaryProjectedController runtime) machine.adversaryLimits
      .adversary machine.adversaryFuel emptyOracle
      (machine.blackBox.start hidden machine.observation)
    rw [returnedRun] at preserved
    simpa [emptyOracle] using preserved
  have rootFinalCovered :
      TableCoveredByQueryOrProgramming runtime.proverFinalOracle := by
    have preserved :=
      run_machine_preserves_table_covered_by_query_or_programming
        (rootAdversaryProjectedController runtime) machine.adversaryLimits
        .adversary machine.adversaryFuel emptyOracle
        (machine.blackBox.start hidden machine.observation)
        empty_oracle_table_covered_by_query_or_programming
    rw [returnedRun] at preserved
    exact preserved
  have returnedHalt :
      (runMachine (rootAdversaryProjectedController runtime)
        machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
        (machine.blackBox.start hidden machine.observation)).halt =
          .returned runtime.adversaryValue := by
    rw [returnedRun]
  cases occurrenceExact : firstEitherInputOccurrence outputInput advanceInput
      runtime.node.proverHistory with
  | none =>
      let prepared : PreparedConcreteRestoration Statement Proof Payload :=
        { request := { nodeId := 0, verifierTransitionIndex := transitionIndex }
          parentNode := runtime.node
          transition := transition
          restoredState := restoreIndexedTransition transition
          outputInput := outputInput
          advanceInput := advanceInput
          occurrence := none
          prefixRun := none
          programmingBase := runtime.node.proverFinalOracle
          prefixSteps := 0 }
      refine ⟨prepared, ?_, ?_, ?_, ?_, ?_⟩
      · simp [prepareConcreteRestorationFromStartProgram, rootStored,
          transitionExact, pairExact, occurrenceExact, prepared]
      · exact rootFinalCoherent
      · simpa [prepared, SchedulerNativePlainRomRootRuntime.node,
          ConcreteRestorationNode.proverHistory, historySince, emptyOracle]
          using occurrenceExact
      · simpa [prepared, SchedulerNativePlainRomRootRuntime.node] using
          rootFinalProgrammingEmpty
      · simpa [prepared, SchedulerNativePlainRomRootRuntime.node] using
          rootFinalCovered
  | some occurrence =>
      have occurrenceSpec := first_either_input_occurrence_spec outputInput
        advanceInput runtime.node.proverHistory occurrence occurrenceExact
      have occurrenceDecomposition :
          historySince emptyOracle
              (runMachine (rootAdversaryProjectedController runtime)
                machine.adversaryLimits .adversary machine.adversaryFuel
                emptyOracle
                (machine.blackBox.start hidden machine.observation)).oracle =
            occurrence.before ++ occurrence.chosen :: occurrence.after := by
        rw [returnedRun]
        simpa [SchedulerNativePlainRomRootRuntime.node,
          ConcreteRestorationNode.proverHistory] using occurrenceSpec.1
      have replay := returned_run_first_occurrence_replays_as_extractor
        (rootAdversaryProjectedController runtime) machine.adversaryLimits
        .adversary machine.adversaryFuel emptyOracle
        (machine.blackBox.start hidden machine.observation)
        runtime.adversaryValue occurrence returnedHalt occurrenceDecomposition
      rcases replay with ⟨pendingContinuation, prefixPaused, prefixTrace⟩
      let prefixRun := runPrefix
        (recordedPrefixController emptyOracle.history.length occurrence.before)
        machine.adversaryLimits .extractorReplay occurrence.before.length
        emptyOracle (machine.blackBox.start hidden machine.observation)
      let prepared : PreparedConcreteRestoration Statement Proof Payload :=
        { request := { nodeId := 0, verifierTransitionIndex := transitionIndex }
          parentNode := runtime.node
          transition := transition
          restoredState := restoreIndexedTransition transition
          outputInput := outputInput
          advanceInput := advanceInput
          occurrence := some occurrence
          prefixRun := some prefixRun
          programmingBase := prefixRun.oracle
          prefixSteps := prefixRun.steps }
      have rootEntry : runtime.node.proverEntryOracle = emptyOracle := rfl
      have beforeNone : firstEitherInputOccurrence outputInput advanceInput
          occurrence.before = none := by
        apply (first_either_input_occurrence_none_iff outputInput advanceInput
          occurrence.before).mpr
        exact occurrenceSpec.2.1
      have prefixNone : firstEitherInputOccurrence outputInput advanceInput
          prefixRun.oracle.history = none := by
        have suffixNone := first_either_none_of_query_answer_trace_eq_root
          outputInput advanceInput (historySince emptyOracle prefixRun.oracle)
          occurrence.before prefixTrace beforeNone
        simpa [historySince, emptyOracle] using suffixNone
      have prefixProgrammingEmpty : prefixRun.oracle.programmingHistory = [] := by
        simpa [prefixRun, emptyOracle] using
          (run_prefix_preserves_programming_history
            (recordedPrefixController emptyOracle.history.length
              occurrence.before)
            machine.adversaryLimits .extractorReplay occurrence.before.length
            emptyOracle (machine.blackBox.start hidden machine.observation))
      have prefixCovered :
          TableCoveredByQueryOrProgramming prefixRun.oracle := by
        exact run_prefix_preserves_table_covered_by_query_or_programming
          (recordedPrefixController emptyOracle.history.length
            occurrence.before)
          machine.adversaryLimits .extractorReplay occurrence.before.length
          emptyOracle (machine.blackBox.start hidden machine.observation)
          empty_oracle_table_covered_by_query_or_programming
      refine ⟨prepared, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [prepareConcreteRestorationFromStartProgram, rootStored,
          transitionExact, pairExact, occurrenceExact]
        rw [limitsExact]
        simp [rootEntry, prefixRun, prefixPaused, prefixTrace, prepared]
      · exact run_prefix_preserves_history_total_coherent
          (recordedPrefixController emptyOracle.history.length
            occurrence.before)
          machine.adversaryLimits .extractorReplay occurrence.before.length
          emptyOracle (machine.blackBox.start hidden machine.observation)
          empty_oracle_history_total_coherent
      · simpa [prepared] using prefixNone
      · simpa [prepared] using prefixProgrammingEmpty
      · simpa [prepared] using prefixCovered

/-- A literal root squeeze reaches a programming base at which both exact
SHA inputs are genuinely undefined, even when the adversary queried one of
them first in the original run. -/
theorem literal_root_squeeze_request_prepares_pair_lookups_none
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type u}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (runs : RootProjectedTotalizedRuns machine hidden runtime)
    (configuration : ConcreteRestorationConfiguration)
    (limitsExact : configuration.oracleLimits = machine.adversaryLimits)
    (transitionIndex : Nat)
    (transition : FutureFreeTransition)
    (transitionExact : verifierTransitionAt? runtime.node transitionIndex =
      some transition)
    (outputInput advanceInput : ShaInput)
    (pairExact : squeezePairInputsOfTransition transition =
      some (outputInput, advanceInput))
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (rootStored : accumulator.node? 0 = some runtime.node) :
    ∃ prepared : PreparedConcreteRestoration Statement Proof Payload,
      prepareConcreteRestorationFromStartProgram
          (machine.blackBox.start hidden machine.observation) configuration
          accumulator
          { nodeId := 0, verifierTransitionIndex := transitionIndex } =
        .ready prepared ∧
      HistoryTotalCoherent prepared.programmingBase ∧
      lookupEntry prepared.programmingBase prepared.outputInput = none ∧
      lookupEntry prepared.programmingBase prepared.advanceInput = none := by
  obtain ⟨prepared, ready, coherent, queryAbsent, programmingEmpty, covered⟩ :=
    literal_root_squeeze_request_prepares_ready_coherent machine hidden runtime
      runs configuration limitsExact transitionIndex transition transitionExact
      outputInput advanceInput pairExact accumulator rootStored
  exact ⟨prepared, ready, coherent,
    pair_lookups_none_of_query_absent_and_programming_empty
      prepared.programmingBase prepared.outputInput prepared.advanceInput
      covered queryAbsent programmingEmpty⟩

/-- Every scheduler-selected 512-bit fork pair can now be installed at the
literal root-squeeze checkpoint.  The adversary-first case is included: the
prefix replay has moved the programming base to just before first exposure. -/
theorem literal_root_squeeze_request_programs_every_fork_pair
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type u}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (runs : RootProjectedTotalizedRuns machine hidden runtime)
    (configuration : ConcreteRestorationConfiguration)
    (limitsExact : configuration.oracleLimits = machine.adversaryLimits)
    (transitionIndex : Nat)
    (transition : FutureFreeTransition)
    (transitionExact : verifierTransitionAt? runtime.node transitionIndex =
      some transition)
    (outputInput advanceInput : ShaInput)
    (pairExact : squeezePairInputsOfTransition transition =
      some (outputInput, advanceInput))
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (rootStored : accumulator.node? 0 = some runtime.node)
    (forkOutput forkAdvance : Digest256)
    (programmingRoom : 2 ≤
      configuration.oracleLimits.programmedPoints) :
    ∃ (prepared : PreparedConcreteRestoration Statement Proof Payload)
        (afterBoth : OracleState),
      prepareConcreteRestorationFromStartProgram
          (machine.blackBox.start hidden machine.observation) configuration
          accumulator
          { nodeId := 0, verifierTransitionIndex := transitionIndex } =
        .ready prepared ∧
      HistoryTotalCoherent prepared.programmingBase ∧
      programConcretePair configuration.oracleLimits
          configuration.pairProgrammingOrder prepared.programmingBase
          prepared.outputInput prepared.advanceInput forkOutput forkAdvance =
        .ready afterBoth := by
  obtain ⟨prepared, ready, coherent, queryAbsent, programmingEmpty, covered⟩ :=
    literal_root_squeeze_request_prepares_ready_coherent machine hidden runtime
      runs configuration limitsExact transitionIndex transition transitionExact
      outputInput advanceInput pairExact accumulator rootStored
  have lookups := pair_lookups_none_of_query_absent_and_programming_empty
    prepared.programmingBase prepared.outputInput prepared.advanceInput
    covered queryAbsent programmingEmpty
  have preparedPair := prepare_from_start_ready_pair_inputs_exact
    (machine.blackBox.start hidden machine.observation) configuration accumulator
    { nodeId := 0, verifierTransitionIndex := transitionIndex } prepared ready
  have distinct := squeeze_pair_inputs_of_transition_are_distinct
    prepared.transition prepared.outputInput prepared.advanceInput preparedPair
  obtain ⟨afterBoth, programmed⟩ :=
    program_concrete_pair_succeeds_from_empty_ledger
      configuration.oracleLimits configuration.pairProgrammingOrder
      prepared.programmingBase prepared.outputInput prepared.advanceInput
      forkOutput forkAdvance distinct lookups.1 lookups.2 programmingEmpty
      programmingRoom
  exact ⟨prepared, afterBoth, ready, coherent, programmed⟩

/-- Complete deterministic root-squeeze dispatcher cut.  Preparation and
coherence are proved internally.  The only remaining hypotheses are the two
literal global resource guards; under them the actual dispatcher exposes the
exact pair-fork header. -/
theorem literal_root_squeeze_dispatch_emits_fork
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (runs : RootProjectedTotalizedRuns machine hidden runtime)
    (configuration : ConcreteRestorationConfiguration)
    (limitsExact : configuration.oracleLimits = machine.adversaryLimits)
    (transitionIndex : Nat)
    (transition : FutureFreeTransition)
    (transitionExact : verifierTransitionAt? runtime.node transitionIndex =
      some transition)
    (outputInput advanceInput : ShaInput)
    (pairExact : squeezePairInputsOfTransition transition =
      some (outputInput, advanceInput))
    (environment : FutureFreeEnvironment)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (rootStored : accumulator.node? 0 = some runtime.node)
    (resume : ConcreteRestorationReply →
      ConcreteRestorationAccumulator Statement Proof Payload →
        SchedulerNativeCursor globalOracleCalls
          (ConcreteRestorationClientRun Statement Proof Payload Result)) :
    ∃ prepared : PreparedConcreteRestoration Statement Proof Payload,
      prepareConcreteRestorationFromStartProgram
          (machine.blackBox.start hidden machine.observation) configuration
          accumulator
          { nodeId := 0, verifierTransitionIndex := transitionIndex } =
        .ready prepared ∧
      HistoryTotalCoherent prepared.programmingBase ∧
      (configuration.oracleLimits.totalCalls ≤ globalOracleCalls →
        prepared.programmingBase.history.length + 2 ≤ globalOracleCalls →
        schedulerNativePairForkHeader?
            (dispatchOneConcreteRestoration
              (machine.blackBox.start hidden machine.observation) environment
              configuration accumulator
              { nodeId := 0, verifierTransitionIndex := transitionIndex }
              resume) =
          some (preparedForkHeader configuration prepared)) := by
  obtain ⟨prepared, ready, coherent, _queryFresh, _programmingEmpty,
      _covered⟩ :=
    literal_root_squeeze_request_prepares_ready_coherent
    machine hidden runtime runs configuration limitsExact transitionIndex
    transition transitionExact outputInput advanceInput pairExact accumulator
    rootStored
  refine ⟨prepared, ready, coherent, ?_⟩
  intro globalLimit pairRoom
  unfold dispatchOneConcreteRestoration dispatchConcreteRestoration
  rw [ready]
  exact dispatch_prepared_restoration_emits_pair_fork_header
    (machine.blackBox.start hidden machine.observation) environment
    configuration prepared accumulator resume coherent globalLimit pairRoom

/-- Typed form of the root result.  The owner and block are computed from the
selected verifier transition before either uniform fork answer is exposed,
while the executable cursor is proved to start at the matching `.forkPair`. -/
theorem literal_root_squeeze_dispatch_emits_typed_fork
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (runs : RootProjectedTotalizedRuns machine hidden runtime)
    (configuration : ConcreteRestorationConfiguration)
    (limitsExact : configuration.oracleLimits = machine.adversaryLimits)
    (transitionIndex : Nat)
    (transition : FutureFreeTransition)
    (transitionExact : verifierTransitionAt? runtime.node transitionIndex =
      some transition)
    (outputInput advanceInput : ShaInput)
    (pairExact : squeezePairInputsOfTransition transition =
      some (outputInput, advanceInput))
    (environment : FutureFreeEnvironment)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (rootStored : accumulator.node? 0 = some runtime.node)
    (resume : ConcreteRestorationReply →
      ConcreteRestorationAccumulator Statement Proof Payload →
        SchedulerNativeCursor globalOracleCalls
          (ConcreteRestorationClientRun Statement Proof Payload Result)) :
    ∃ (prepared : PreparedConcreteRestoration Statement Proof Payload)
        (role : PreparedRestorationPairRole),
      prepareConcreteRestorationFromStartProgram
          (machine.blackBox.start hidden machine.observation) configuration
          accumulator
          { nodeId := 0, verifierTransitionIndex := transitionIndex } =
        .ready prepared ∧
      HistoryTotalCoherent prepared.programmingBase ∧
      preparedRestorationPairRole? prepared = some role ∧
      role.inputs = (prepared.outputInput, prepared.advanceInput) ∧
      role.outputInput =
        bytes prepared.transition.before.core.digest ++ [domSqueeze] ∧
      role.advanceInput =
        bytes prepared.transition.before.core.digest ++ [domAdvance] ∧
      (configuration.oracleLimits.totalCalls ≤ globalOracleCalls →
        prepared.programmingBase.history.length + 2 ≤ globalOracleCalls →
        schedulerNativePairForkHeader?
            (dispatchOneConcreteRestoration
              (machine.blackBox.start hidden machine.observation) environment
              configuration accumulator
              { nodeId := 0, verifierTransitionIndex := transitionIndex }
              resume) =
          some (preparedForkHeader configuration prepared)) := by
  obtain ⟨prepared, ready, coherent, emits⟩ :=
    literal_root_squeeze_dispatch_emits_fork machine hidden runtime runs
      configuration limitsExact transitionIndex transition transitionExact
      outputInput advanceInput pairExact environment accumulator rootStored
      resume
  obtain ⟨role, projected, inputs, outputExact, advanceExact⟩ :=
    ready_preparation_has_pair_role
      (machine.blackBox.start hidden machine.observation) configuration
      accumulator { nodeId := 0, verifierTransitionIndex := transitionIndex }
      prepared ready
  exact ⟨prepared, role, ready, coherent, projected, inputs, outputExact,
    advanceExact, emits⟩

#print axioms successful_query_preserves_history_total_coherent
#print axioms run_prefix_preserves_history_total_coherent
#print axioms run_machine_preserves_history_total_coherent
#print axioms pair_lookups_none_of_query_absent_and_programming_empty
#print axioms program_concrete_pair_succeeds_from_empty_ledger
#print axioms schedulerNativePairForkHeader?
#print axioms dispatch_prepared_restoration_emits_pair_fork_header
#print axioms literal_root_squeeze_request_prepares_ready_coherent
#print axioms literal_root_squeeze_request_prepares_pair_lookups_none
#print axioms literal_root_squeeze_request_programs_every_fork_pair
#print axioms literal_root_squeeze_dispatch_emits_fork
#print axioms literal_root_squeeze_dispatch_emits_typed_fork

end

end AspisK1.V7Tag73RootSqueezeForkEmission

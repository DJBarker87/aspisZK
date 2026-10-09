import FSV8AlphaRouterRealization
import AspisFormal.K1.V7Tag73SchedulerNativeResult

/-!
# Constructing the V8 alpha labelled trace from one actual root prefix

This is the V8 specialization of the chronological construction pattern in
`V7Tag73IndexedControllerLabeledRecords` and
`V7Tag73ExactCandidateLabeledRootRouting`.  Starting at the literal
`exposureCursor`, it asks the actual alpha pre-answer machine for its label,
then advances that same cursor with the answer carried by the next root
record.

The main constructor consumes an equality saying that `records` is a
chronological prefix of the *actual* exact-root trace.  It derives both the
`MachineLabeledTrace` and the corresponding master-tape prefix equality.
Named-label uniqueness and residual capacity are deliberately separate
premises: this file neither assumes freshness nor proves the source-specific
alpha inclusion and probability bounds.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 1800

namespace AspisV8Completion.FSV8AlphaRootLabeledTraceConstructor

open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalSlotMachineRouter
open AspisK1.V7Tag73ExactCausalRouterTapeAlignment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73K15RelationAlphaPreAnswerRouters
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73SchedulerNativeResult
open FSV8AlphaRouterRealization
open FSV8ExactRootCursor

noncomputable section

universe u

abbrev Block := FSBoundedTranscript.Block

/-- Replay chronological answers through a pre-answer machine, recording the
label selected before each answer.  This is the unindexed state specialization
of `indexedControllerLabeledRecords`. -/
def machineLabeledAnswers
    {Output Slot : Type} {State : Type u}
    (machine : PreAnswerSlotMachine Output Slot State) :
    State → List Output → List (Option Slot × Output)
  | _state, [] => []
  | state, answer :: answers =>
      (machine.preferredSlot state, answer) ::
        machineLabeledAnswers machine (machine.afterAnswer state answer) answers

/-- The cursor reached after consuming the same chronological answer list. -/
def machineStateAfterAnswers
    {Output Slot : Type} {State : Type u}
    (machine : PreAnswerSlotMachine Output Slot State) :
    State → List Output → State
  | state, [] => state
  | state, answer :: answers =>
      machineStateAfterAnswers machine (machine.afterAnswer state answer) answers

/-- Forgetting the labels recovers the literal chronological answers. -/
theorem machine_labeled_answers_map_snd
    {Output Slot : Type} {State : Type u}
    (machine : PreAnswerSlotMachine Output Slot State) :
    ∀ (state : State) (answers : List Output),
      (machineLabeledAnswers machine state answers).map Prod.snd = answers := by
  intro state answers
  induction answers generalizing state with
  | nil => rfl
  | cons answer answers ih =>
      simp only [machineLabeledAnswers, List.map_cons]
      rw [ih]

/-- The generated labels form an execution of exactly the supplied
pre-answer machine, with no source or freshness hypothesis. -/
theorem machine_labeled_answers_form_trace
    {Output Slot : Type} {State : Type u}
    (machine : PreAnswerSlotMachine Output Slot State) :
    ∀ (state : State) (answers : List Output),
      MachineLabeledTrace machine state
        (machineLabeledAnswers machine state answers)
        (machineStateAfterAnswers machine state answers) := by
  intro state answers
  induction answers generalizing state with
  | nil => exact .nil state
  | cons answer answers ih =>
      exact .cons rfl (ih (machine.afterAnswer state answer))

/-- Literal V8 alpha labels over the answers of one chronological root-record
prefix.  Record kinds and actors remain in `records`; only their already
exposed answers drive the pre-answer state transition. -/
def alpha0RootLabeledRecords
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      globalOracleCalls n m)
    (transitionFuel : Nat) (hidden : HiddenTape)
    (records : List UnifiedExposureRecord) :
    List (Option RelationAlphaDuplexSlot × Block) :=
  machineLabeledAnswers (relationAlphaSlotMachine 0 transitionFuel)
    (exposureCursor configuration hidden)
    (records.map UnifiedExposureRecord.answer)

/-- The V8-labelled record answers are exactly the underlying root-record
answers. -/
theorem alpha0_root_labeled_records_answers
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      globalOracleCalls n m)
    (transitionFuel : Nat) (hidden : HiddenTape)
    (records : List UnifiedExposureRecord) :
    (alpha0RootLabeledRecords configuration transitionFuel hidden records).map
        Prod.snd = records.map UnifiedExposureRecord.answer := by
  exact machine_labeled_answers_map_snd
    (relationAlphaSlotMachine 0 transitionFuel)
    (exposureCursor configuration hidden)
    (records.map UnifiedExposureRecord.answer)

/-- The chronological V8 labels execute the exact alpha slot machine from the
exact same-body root exposure cursor. -/
theorem alpha0_root_labeled_records_form_trace
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      globalOracleCalls n m)
    (transitionFuel : Nat) (hidden : HiddenTape)
    (records : List UnifiedExposureRecord) :
    MachineLabeledTrace (relationAlphaSlotMachine 0 transitionFuel)
      (exposureCursor configuration hidden)
      (alpha0RootLabeledRecords configuration transitionFuel hidden records)
      (machineStateAfterAnswers (relationAlphaSlotMachine 0 transitionFuel)
        (exposureCursor configuration hidden)
        (records.map UnifiedExposureRecord.answer)) := by
  exact machine_labeled_answers_form_trace
    (relationAlphaSlotMachine 0 transitionFuel)
    (exposureCursor configuration hidden)
    (records.map UnifiedExposureRecord.answer)

/-- An actual chronological prefix of the exact V8 root consumes the same
prefix of the one master answer tape.  The suffix is derived from the actual
root trace; it is not selected independently. -/
theorem actual_alpha0_root_prefix_answers_master_tape
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat)
    (sample : ExactCompilerSample HiddenTape parameters)
    (records later : List UnifiedExposureRecord)
    (traceExact :
      (runExactRoot parameters configuration transitionFuel sample).trace =
        records ++ later) :
    freshAnswerTapeToList sample.2 =
      (alpha0RootLabeledRecords configuration transitionFuel sample.1
        records).map Prod.snd ++ later.map UnifiedExposureRecord.answer := by
  have answersExact := run_scheduler_native_answers_are_exact_tape
    transitionFuel (exactCompilerTargetCaps parameters).length
    (rootCursor configuration sample.1) sample.2
  change (runExactRoot parameters configuration transitionFuel sample).trace.map
      UnifiedExposureRecord.answer = freshAnswerTapeToList sample.2 at answersExact
  rw [traceExact, List.map_append] at answersExact
  rw [alpha0_root_labeled_records_answers]
  exact answersExact.symm

/-- Construct the operational fields of `Alpha0RootLabeledTrace` from one
actual root prefix.  Only the two finite routing side conditions remain as
explicit inputs.  In particular, neither accepted alpha inclusion nor any
freshness/probability statement is smuggled into this constructor. -/
def actualRootPrefixAlpha0RootLabeledTrace
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat)
    (sample : ExactCompilerSample HiddenTape parameters)
    (records later : List UnifiedExposureRecord)
    (traceExact :
      (runExactRoot parameters configuration transitionFuel sample).trace =
        records ++ later)
    (namedNodup :
      (namedTraceSlots (alpha0RootLabeledRecords configuration transitionFuel
        sample.1 records)).Nodup)
    (residualEnough :
      residualTraceSteps (alpha0RootLabeledRecords configuration transitionFuel
        sample.1 records) ≤ relationAlphaRouterResidual parameters) :
    Alpha0RootLabeledTrace parameters configuration transitionFuel sample.1
      sample.2 := by
  exact {
    steps := alpha0RootLabeledRecords configuration transitionFuel sample.1
      records
    finalCursor := machineStateAfterAnswers
      (relationAlphaSlotMachine 0 transitionFuel)
      (exposureCursor configuration sample.1)
      (records.map UnifiedExposureRecord.answer)
    remaining := later.map UnifiedExposureRecord.answer
    trace := alpha0_root_labeled_records_form_trace configuration transitionFuel
      sample.1 records
    namedNodup := namedNodup
    residualEnough := residualEnough
    tapePrefix := by
      rw [fresh_answer_tape_to_list_cast]
      exact actual_alpha0_root_prefix_answers_master_tape parameters
        configuration transitionFuel sample records later traceExact }

#print axioms machine_labeled_answers_map_snd
#print axioms machine_labeled_answers_form_trace
#print axioms alpha0_root_labeled_records_answers
#print axioms alpha0_root_labeled_records_form_trace
#print axioms actual_alpha0_root_prefix_answers_master_tape
#print axioms actualRootPrefixAlpha0RootLabeledTrace

end
end AspisV8Completion.FSV8AlphaRootLabeledTraceConstructor

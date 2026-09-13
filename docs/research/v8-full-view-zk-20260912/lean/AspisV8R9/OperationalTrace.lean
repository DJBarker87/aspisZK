import AspisV8R9.OperationalLaws

/-!
# Operational machine to R8 forward traces

The good predicate below is the exact local complement of the commitment-hop
failures: an ordinary query addresses a deferred input, a new reservation is
already cached on either side, or delayed paired installation conflicts.
Aborts caused equally on both sides remain ordinary public observations.
-/
set_option autoImplicit false
namespace AspisV8R9
open AspisV8PairedCommitment

variable {I A : Type} [DecidableEq I] [DecidableEq A]

def toForward (state : Machine I A × Machine I A) :
    ForwardState I A (Observation I A) :=
  { eager := state.1.table
    delayed := state.2.table
    hidden := state.1.hidden
    eagerView := state.1.view
    delayedView := state.2.view }

def EagerPendingCached (state : Machine I A) : Prop :=
  ∀ slot input answer, state.pending slot = some (input, answer) →
    state.table input = some answer

def OperationalInvariant (state : Machine I A × Machine I A) : Prop :=
  EagerPendingCached state.1 ∧
    state.1.pending = state.2.pending ∧
    state.1.hidden = state.2.hidden ∧
    state.1.stopped = state.2.stopped ∧
    ForwardInvariant (toForward state)

def CommandGood (state : Machine I A × Machine I A) (command : Command I) : Prop :=
  state.1.stopped = true ∨ match command with
    | .query input => ¬ state.1.hidden input
    | .reserve slot input =>
        match state.1.pending slot with
        | some _ => True
        | none => state.1.table input = none ∧ state.2.table input = none
    | .openPair left right =>
        match state.1.pending left, state.1.pending right with
        | some (i, a), some (j, b) =>
            i = j ∨ (installPair state.2.table i j a b).2 = true
        | _, _ => True
    | .emit _ => True
    | .halt => True

def operationalBad (state : Machine I A × Machine I A) (command : Command I) : Prop :=
  ¬ CommandGood state command

def jointAdvance (state : Machine I A × Machine I A)
    (command : Command I) (fresh : A) : Machine I A × Machine I A :=
  (advance .eager state.1 command fresh, advance .delayed state.2 command fresh)

def traceObserve : A → Observation I A := fun answer => .reserved 0 answer

private theorem singleTrace
    {before after : ForwardState I A (Observation I A)}
    (step : ForwardStep traceObserve before after) :
    ForwardTrace traceObserve before after :=
  .tail step (.refl after)

/-- A good step of the explicit eager/delayed interpreters constructs the R8
transition; no caller-supplied final execution or trace witness appears. -/
theorem jointAdvance_forward
    (state : Machine I A × Machine I A) (command : Command I) (fresh : A)
    (invariant : OperationalInvariant state) (good : CommandGood state command) :
    ForwardTrace traceObserve (toForward state)
      (toForward (jointAdvance state command fresh)) := by
  rcases invariant with ⟨pendingCached, pendingEq, hiddenEq, stoppedEq, forward⟩
  rcases forward with ⟨agree, viewsEq⟩
  by_cases stopped : state.1.stopped = true
  · have rightStopped : state.2.stopped = true := stoppedEq ▸ stopped
    simpa [jointAdvance, toForward, advance, stopped, rightStopped] using
      (ForwardTrace.refl (observe := traceObserve) (toForward state))
  have running : state.1.stopped = false := Bool.eq_false_of_not_eq_true (by
    intro isStopped
    exact stopped isStopped)
  have rightRunning : state.2.stopped = false := stoppedEq ▸ running
  cases command with
  | halt =>
      apply singleTrace
      simpa [jointAdvance, toForward, advance, running, rightRunning] using
        (ForwardStep.emit (observe := traceObserve) (toForward state)
          (Observation.halt : Observation I A))
  | emit value =>
      apply singleTrace
      simpa [jointAdvance, toForward, tick, advance, appendObservation,
        running, rightRunning] using
        (ForwardStep.emit (observe := traceObserve) (toForward state)
          (Observation.emit value : Observation I A))
  | query input =>
      have queryGood : ¬ state.1.hidden input := by
        simpa [CommandGood, stopped] using good
      have answers := ordinary_query_agrees state.1.hidden state.1.table state.2.table
        input fresh agree queryGood
      apply singleTrace
      simpa [jointAdvance, toForward, advance, appendObservation, running,
        rightRunning, answers.1] using
        (ForwardStep.ordinaryRecord (observe := traceObserve) (toForward state)
          input fresh (.answer input (queryStep state.1.table input fresh).1) queryGood)
  | reserve slot input =>
      cases leftPending : state.1.pending slot with
      | some old =>
          have rightPending : state.2.pending slot = some old := by
            rw [← pendingEq]
            exact leftPending
          rcases old with ⟨oldInput, oldAnswer⟩
          by_cases same : oldInput = input
          · apply singleTrace
            simpa [jointAdvance, toForward, advance, appendObservation, running,
              rightRunning, leftPending, rightPending, same] using
              (ForwardStep.emit (observe := traceObserve) (toForward state)
                (.reserved slot oldAnswer))
          · apply singleTrace
            simpa [jointAdvance, toForward, advance, abortMachine, running,
              rightRunning, leftPending, rightPending, same] using
              (ForwardStep.emit (observe := traceObserve) (toForward state)
                (.abort 1))
      | none =>
          have reserveGood : state.1.table input = none ∧ state.2.table input = none := by
            simpa [CommandGood, stopped, leftPending] using good
          have missingLeft : state.1.table input = none := reserveGood.1
          have missingRight : state.2.table input = none := reserveGood.2
          have rightPending : state.2.pending slot = none := by
            rw [← pendingEq]
            exact leftPending
          apply singleTrace
          simpa [jointAdvance, toForward, advance, appendObservation, running,
            rightRunning, leftPending, rightPending, queryStep, missingLeft,
            missingRight] using
            (ForwardStep.deferRecord (observe := traceObserve) (toForward state)
              input fresh (.reserved slot fresh) missingLeft missingRight)
  | openPair left right =>
      cases leftRecord : state.1.pending left with
      | none =>
          have rightRecord : state.2.pending left = none := by
            rw [← pendingEq]
            exact leftRecord
          apply singleTrace
          simpa [jointAdvance, toForward, advance, abortMachine, running,
            rightRunning, leftRecord, rightRecord] using
            (ForwardStep.emit (observe := traceObserve) (toForward state) (.abort 4))
      | some first =>
          have rightFirst : state.2.pending left = some first := by
            rw [← pendingEq]
            exact leftRecord
          cases rightRecord : state.1.pending right with
          | none =>
              have delayedRight : state.2.pending right = none := by
                rw [← pendingEq]
                exact rightRecord
              apply singleTrace
              simpa [jointAdvance, toForward, advance, abortMachine, running,
                rightRunning, leftRecord, rightRecord, rightFirst, delayedRight] using
                (ForwardStep.emit (observe := traceObserve) (toForward state) (.abort 4))
          | some second =>
              have delayedSecond : state.2.pending right = some second := by
                rw [← pendingEq]
                exact rightRecord
              rcases first with ⟨i, a⟩
              rcases second with ⟨j, b⟩
              by_cases same : i = j
              · apply singleTrace
                simpa [jointAdvance, toForward, advance, abortMachine, running,
                  rightRunning, leftRecord, rightRecord, rightFirst, delayedSecond,
                  same] using
                  (ForwardStep.emit (observe := traceObserve) (toForward state) (.abort 2))
              · have success : (installPair state.2.table i j a b).2 = true :=
                  (by
                    have pairGood : i = j ∨
                        (installPair state.2.table i j a b).2 = true := by
                      simpa [CommandGood, stopped, leftRecord, rightRecord] using good
                    exact pairGood.resolve_left same)
                apply singleTrace
                simpa [jointAdvance, toForward, advance, appendObservation, running,
                  rightRunning, leftRecord, rightRecord, rightFirst, delayedSecond,
                  same, success] using
                  (ForwardStep.materialize (observe := traceObserve) (toForward state)
                    i j a b (.opened i a j b)
                    (pendingCached left i a leftRecord)
                    (pendingCached right j b rightRecord) success)

def runSchedule : List (Command I × A) →
    (Machine I A × Machine I A) → Machine I A × Machine I A
  | [], state => state
  | (command, fresh) :: rest, state =>
      runSchedule rest (jointAdvance state command fresh)

/-- A source prefix is admissible only when every actual interpreter state
satisfies the operational invariant and its next command avoids the exact bad
predicate.  In particular this does not accept a separately supplied synthetic
`ForwardTrace`. -/
inductive NonBadOperationalPrefix :
    (Machine I A × Machine I A) → List (Command I × A) → Prop
  | nil (state : Machine I A × Machine I A)
      (invariant : OperationalInvariant state) :
      NonBadOperationalPrefix state []
  | cons (state : Machine I A × Machine I A) (command : Command I) (fresh : A)
      (schedule : List (Command I × A))
      (invariant : OperationalInvariant state)
      (good : CommandGood state command)
      (rest : NonBadOperationalPrefix (jointAdvance state command fresh) schedule) :
      NonBadOperationalPrefix state ((command, fresh) :: schedule)

private theorem forwardTrace_trans
    {first middle last : ForwardState I A (Observation I A)}
    (traceFirst : ForwardTrace traceObserve first middle)
    (suffix : ForwardTrace traceObserve middle last) :
    ForwardTrace traceObserve first last := by
  induction traceFirst with
  | refl => exact suffix
  | tail step rest ih => exact .tail step (ih suffix)

/-- Iterating the operational bridge yields the existing R8 forward-trace
theorem for the actual eager/delayed command prefix. -/
theorem nonbad_prefix_forward
    (state : Machine I A × Machine I A) (schedule : List (Command I × A))
    (nonbad : NonBadOperationalPrefix state schedule) :
    ForwardTrace traceObserve (toForward state)
      (toForward (runSchedule schedule state)) := by
  induction nonbad with
  | nil => exact .refl _
  | @cons state command fresh schedule invariant good rest ih =>
      exact forwardTrace_trans (jointAdvance_forward state command fresh invariant good) ih

#print axioms jointAdvance_forward
#print axioms nonbad_prefix_forward
end AspisV8R9

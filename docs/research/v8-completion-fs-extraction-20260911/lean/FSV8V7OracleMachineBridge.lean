import FSV8FiniteInterpreterEventBridge
import AspisFormal.K1.V7Tag73OperationalOracleExposure

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8V7OracleMachineBridge
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block

/-- Structural compilation only. `Script.abort` is represented by the explicit
    V7 refusal halt; no source/adversary semantics are inferred from this
    choice. -/
def compileScript {A : Type} : {n : Nat} →
    Script Bytes Block A n → OracleMachine A
  | _, .done value => .pure value
  | _, .abort => .abort .controllerRefused
  | _, .ask input next => .query input (fun output => compileScript (next output))

def projectOrigin : AnswerOrigin → Bool
  | .fresh => true
  | .programmed => false
  | .cached => false

def projectRecord (record : QueryRecord) : Event Bytes Block :=
  { input := record.input, answer := record.output,
    fresh := projectOrigin record.origin }

def projectedCache (state : OracleState) : Bytes → Option Block :=
  fun input => (lookupEntry state input).map TableEntry.output

def projectOracleState (state : OracleState) : State Bytes Block where
  cache := projectedCache state
  next := state.freshCalls
  log := state.history.map projectRecord

theorem compileScript_done {A : Type} (value : A) :
    compileScript (.done value : Script Bytes Block A 0) = .pure value := rfl

theorem compileScript_abort {A : Type} :
    compileScript (.abort : Script Bytes Block A 0) = .abort .controllerRefused := rfl

theorem compileScript_ask {A : Type} {n : Nat} (input : Bytes)
    (next : Block → Script Bytes Block A n) :
    compileScript (.ask input next) = .query input
      (fun output => compileScript (next output)) := rfl

theorem projectOracleState_empty :
    projectOracleState emptyOracle =
      (FSFirstFresh.empty : State Bytes Block) := by
  rfl

def singletonFreshState (actor : QueryActor) (input : Bytes)
    (answer : Block) : OracleState where
  table := [{ input := input, output := answer, source := .fresh }]
  history := [{ input := input, output := answer, actor := actor, origin := .fresh }]
  programmingHistory := []
  totalCalls := 1
  freshCalls := 1

theorem projected_empty_query_fresh
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (input : Bytes) (answer : Block)
    (tape : Nat → Block)
    (controller_answer : controller [] input = .answer answer)
    (total_ok : 0 < limits.totalCalls) (fresh_ok : 0 < limits.freshCalls)
    (tape_answer : tape 0 = answer) :
    queryOracle controller limits actor emptyOracle input =
      .ok (answer, singletonFreshState actor input answer) ∧
    projectOracleState (singletonFreshState actor input answer) =
      (FSOracleExecution.query tape (FSFirstFresh.empty : State Bytes Block) input).2 := by
  constructor
  · simp [queryOracle, emptyOracle, lookupEntry, controller_answer,
      Nat.not_le.mpr total_ok, Nat.not_le.mpr fresh_ok, singletonFreshState]
  · have cacheEq :
        projectedCache (singletonFreshState actor input answer) =
        (fun other => if other = input then some answer else none) := by
      funext other
      by_cases same : other = input
      · subst other
        simp [projectedCache, lookupEntry, singletonFreshState]
      · simp [projectedCache, lookupEntry, singletonFreshState, same, Ne.symm same]
    simp only [projectOracleState, FSOracleExecution.query, FSFirstFresh.empty]
    rw [tape_answer, cacheEq]
    simp [singletonFreshState, projectRecord, projectOrigin]

theorem projected_empty_query_cached
    (actor : QueryActor) (input : Bytes) (answer : Block)
    (tape : Nat → Block) :
    let state : OracleState := singletonFreshState actor input answer
    queryOracle (fun _ _ => .refuse)
      { totalCalls := 2, freshCalls := 1, programmedPoints := 0 }
      actor state input =
      .ok (answer, { state with
        history := state.history ++
          [{ input := input, output := answer, actor, origin := .cached }]
        totalCalls := 2 }) := by
  simp [queryOracle, lookupEntry, cachedOrigin, singletonFreshState]

/-- The remaining semantic gap is explicit: `projectOracleState` preserves the
    table-derived cache, ordered history, and fresh counter, but a full query
    refinement additionally needs a V7 controller/limits object matching the
    Script tape interpreter's refusal/exhaustion behavior. -/
def projectedQueryInput (state : OracleState) (input : Bytes) :
    Option Block := (lookupEntry state input).map TableEntry.output

#print axioms compileScript_done
#print axioms compileScript_abort
#print axioms compileScript_ask
#print axioms projectOracleState_empty
#print axioms projected_empty_query_fresh
#print axioms projected_empty_query_cached
end AspisV8Completion.FSV8V7OracleMachineBridge

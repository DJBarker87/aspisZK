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

def projectOracleState (state : OracleState) : State Bytes Block where
  cache := fun input => (lookupEntry state input).map TableEntry.output
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
end AspisV8Completion.FSV8V7OracleMachineBridge

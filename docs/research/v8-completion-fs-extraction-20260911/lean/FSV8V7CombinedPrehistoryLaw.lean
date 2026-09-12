import FSV8V7PrehistoryContinuation

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8V7CombinedPrehistoryLaw
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open FSV8V7OracleMachineBridge FSV8V7WholeScriptAlignment
open FSV8V7WholeScriptUniformLaw FSV8V7PrehistoryContinuation

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block

structure CombinedOutcome (A B : Type) where
  preHalt : MachineHalt A
  postHalt : Option (ScriptHalt B)
  postState : State Bytes Block

def combinedCurrent {A B : Type} {steps n : Nat}
    (finiteTape : FreshAnswerTape Block steps) (fallback : Block)
    (limits : OracleLimits) (actor : QueryActor)
    (preFuel : Nat) (preProgram : OracleMachine A)
    (script : Script Bytes Block B n) : CombinedOutcome A B :=
  let pre := prehistoryRun steps limits actor preFuel preProgram finiteTape
  let current := run (extendFreshTape finiteTape fallback) script
    (projectOracleState pre.oracle)
  { preHalt := pre.halt
    postHalt := some (currentHalt current.1)
    postState := current.2 }

def combinedV7 {A B : Type} {steps n : Nat}
    (finiteTape : FreshAnswerTape Block steps) (fallback : Block)
    (limits : OracleLimits) (actor : QueryActor)
    (preFuel : Nat) (preProgram : OracleMachine A)
    (script : Script Bytes Block B n) : CombinedOutcome A B :=
  let pre := prehistoryRun steps limits actor preFuel preProgram finiteTape
  let continued := runMachine (controllerFromFreshAnswerTape finiteTape)
    limits actor n pre.oracle (compileScript script)
  { preHalt := pre.halt
    postHalt := machineHalt continued.halt
    postState := projectOracleState continued.oracle }

theorem combined_pointwise_eq
    {A B : Type} {steps n : Nat}
    (finiteTape : FreshAnswerTape Block steps) (fallback : Block)
    (limits : OracleLimits) (actor : QueryActor)
    (preFuel : Nat) (preProgram : OracleMachine A)
    (script : Script Bytes Block B n)
    (totalRoom :
      (prehistoryRun steps limits actor preFuel preProgram finiteTape).oracle.totalCalls + n ≤
        limits.totalCalls)
    (freshRoom :
      (prehistoryRun steps limits actor preFuel preProgram finiteTape).oracle.freshCalls + n ≤
        limits.freshCalls)
    (tapeRoom :
      (projectOracleState
          (prehistoryRun steps limits actor preFuel preProgram finiteTape).oracle).next + n ≤
        steps) :
    combinedCurrent finiteTape fallback limits actor preFuel preProgram script =
      combinedV7 finiteTape fallback limits actor preFuel preProgram script := by
  have exact := continue_from_uniform_prehistory_exact finiteTape fallback limits actor
    preFuel preProgram script totalRoom freshRoom tapeRoom
  rcases exact with ⟨haltEq, stateEq⟩
  simp only [combinedCurrent, combinedV7]
  rw [haltEq, stateEq]

noncomputable def combinedCurrentLaw {A B : Type} (steps : Nat)
    (fallback : Block) (limits : OracleLimits) (actor : QueryActor)
    (preFuel : Nat) (preProgram : OracleMachine A)
    {n : Nat} (script : Script Bytes Block B n) : PMF (CombinedOutcome A B) :=
  (uniformDigestFreshTape steps).map
    (fun finiteTape => combinedCurrent finiteTape fallback limits actor preFuel
      preProgram script)

noncomputable def combinedV7Law {A B : Type} (steps : Nat)
    (fallback : Block) (limits : OracleLimits) (actor : QueryActor)
    (preFuel : Nat) (preProgram : OracleMachine A)
    {n : Nat} (script : Script Bytes Block B n) : PMF (CombinedOutcome A B) :=
  (uniformDigestFreshTape steps).map
    (fun finiteTape => combinedV7 finiteTape fallback limits actor preFuel
      preProgram script)

theorem combined_current_law_eq_v7_law
    {A B : Type} (steps : Nat) (fallback : Block) (limits : OracleLimits)
    (actor : QueryActor) (preFuel : Nat) (preProgram : OracleMachine A)
    {n : Nat} (script : Script Bytes Block B n)
    (rooms : ∀ finiteTape : FreshAnswerTape Block steps,
      (prehistoryRun steps limits actor preFuel preProgram finiteTape).oracle.totalCalls + n ≤
        limits.totalCalls ∧
      (prehistoryRun steps limits actor preFuel preProgram finiteTape).oracle.freshCalls + n ≤
        limits.freshCalls ∧
      (projectOracleState
          (prehistoryRun steps limits actor preFuel preProgram finiteTape).oracle).next + n ≤
        steps) :
    combinedCurrentLaw steps fallback limits actor preFuel preProgram script =
      combinedV7Law steps fallback limits actor preFuel preProgram script := by
  unfold combinedCurrentLaw combinedV7Law
  congr 1
  funext finiteTape
  exact combined_pointwise_eq finiteTape fallback limits actor preFuel preProgram script
    (rooms finiteTape).1 (rooms finiteTape).2.1 (rooms finiteTape).2.2

#print axioms combined_pointwise_eq
#print axioms combined_current_law_eq_v7_law
end AspisV8Completion.FSV8V7CombinedPrehistoryLaw

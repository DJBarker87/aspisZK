import FSV8V7HistoryProjectionAlignment

/-!
# Continue a finite-tape prehistory with one current V8 script

The prehistory is executed by the V7 lazy-oracle machine from `emptyOracle`.
Its resulting oracle is projected into the current interpreter, and the same
finite tape then drives the current V8 continuation.  The state-alignment
premise is constructed by `uniform_run_projected_state_aligned`; it is not an
input to the theorem.

This remains an ideal finite-tape execution.  It does not construct the
adversary/source prehistory or couple a deployed random oracle to this tape.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8V7PrehistoryContinuation

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open FSV8V7OracleMachineBridge FSV8V7StateAlignment
open FSV8V7WholeScriptAlignment FSV8V7WholeScriptUniformLaw
open FSV8V7HistoryProjectionAlignment

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block

/-- The exact prehistory run used on both sides of the continuation. -/
def prehistoryRun {A : Type} (steps : Nat) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (program : OracleMachine A)
    (finiteTape : FreshAnswerTape Block steps) : MachineRun A :=
  runMachineFromUniformFreshTape steps limits actor fuel program finiteTape

/-- A current V8 continuation from the projected prehistory agrees with the
V7 lazy-oracle execution of its compiled script.  All cache entries, counters,
and chronological history at the cut are produced by the prehistory run.

The three room hypotheses are resource conditions on that produced state;
they are not semantic, acceptance, freshness, or extraction assumptions. -/
theorem continue_from_uniform_prehistory_aligned
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
    let v7 := (prehistoryRun steps limits actor preFuel preProgram finiteTape).oracle
    let fs := projectOracleState v7
    let continued := runMachine (controllerFromFreshAnswerTape finiteTape)
      limits actor n v7 (compileScript script)
    ResultAligned (run (extendFreshTape finiteTape fallback) script fs).1
        continued.halt /\
      StateAligned (extendFreshTape finiteTape fallback) finiteTape
        continued.oracle (run (extendFreshTape finiteTape fallback) script fs).2 := by
  have initialAligned := uniform_run_projected_state_aligned finiteTape fallback
    limits actor preFuel preProgram
  exact run_compileScript_aligned limits actor script
    (prehistoryRun steps limits actor preFuel preProgram finiteTape).oracle
    (projectOracleState
      (prehistoryRun steps limits actor preFuel preProgram finiteTape).oracle)
    initialAligned totalRoom freshRoom tapeRoom

/-- In particular, the projected final oracle state is literally the current
interpreter's final state, and the visible halt classifications coincide. -/
theorem continue_from_uniform_prehistory_exact
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
    let v7 := (prehistoryRun steps limits actor preFuel preProgram finiteTape).oracle
    let fs := projectOracleState v7
    let continued := runMachine (controllerFromFreshAnswerTape finiteTape)
      limits actor n v7 (compileScript script)
    machineHalt continued.halt =
        some (currentHalt (run (extendFreshTape finiteTape fallback) script fs).1) /\
      projectOracleState continued.oracle =
        (run (extendFreshTape finiteTape fallback) script fs).2 := by
  have compared := continue_from_uniform_prehistory_aligned finiteTape fallback
    limits actor preFuel preProgram script totalRoom freshRoom tapeRoom
  exact ⟨resultAligned_machineHalt _ _ compared.1,
    aligned_projectOracleState_eq compared.2⟩

#print axioms continue_from_uniform_prehistory_aligned
#print axioms continue_from_uniform_prehistory_exact

end AspisV8Completion.FSV8V7PrehistoryContinuation

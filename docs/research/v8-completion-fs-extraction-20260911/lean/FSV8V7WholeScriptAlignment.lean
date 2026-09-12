import FSV8V7FreshAlignment

/-!
# Whole bounded-script V8/V7 oracle alignment

Structural deterministic refinement of the current `Script` interpreter to
the V7 `OracleMachine`, using the finite fresh-answer-tape controller.  Cached
and fresh queries are treated separately.  There are no programmed entries,
probability, freshness, or independence claims here.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8V7WholeScriptAlignment

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open FSV8V7OracleMachineBridge FSV8V7StateAlignment
open FSV8V7CachedAlignment FSV8V7FreshAlignment

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape

/-- Exact visible result correspondence.  A source `abort` is compiled to the
explicit V7 controller-refusal halt. -/
def ResultAligned {A : Type} : Option A -> MachineHalt A -> Prop
  | some value, halt => halt = .returned value
  | none, halt => halt = .oracleAbort .controllerRefused

theorem cached_query_success_equation {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps}
    {v7 : OracleState} {fs : State Bytes Block}
    (aligned : StateAligned tape finiteTape v7 fs)
    (limits : OracleLimits) (actor : QueryActor) (input : Bytes)
    (entry : TableEntry) (total_ok : v7.totalCalls < limits.totalCalls)
    (lookup : lookupEntry v7 input = some entry) :
    queryOracle (controllerFromFreshAnswerTape finiteTape) limits actor v7 input =
      .ok (entry.output, cachedSuccessor actor input entry v7) := by
  simp [queryOracle, Nat.not_le.mpr total_ok, lookup, cachedSuccessor]

/-- The complete structural induction.  The index `n` is the static maximum
number of calls, so the three additive hypotheses provide room for every
continuation without a successor assumption supplied from outside.

The V7 machine is run with exactly `n` fuel.  Its return/refusal result equals
the current interpreter's result, and its final oracle remains aligned with
the current final state. -/
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
      · simp [ResultAligned, FSOracleExecution.run, compileScript, runMachine]
      · simpa [FSOracleExecution.run, compileScript, runMachine] using aligned
  | abort =>
      intro v7 fs aligned totalRoom freshRoom tapeRoom
      constructor
      · simp [ResultAligned, FSOracleExecution.run, compileScript, runMachine]
      · simpa [FSOracleExecution.run, compileScript, runMachine] using aligned
  | @ask remaining input next ih =>
      intro v7 fs aligned totalRoom freshRoom tapeRoom
      have totalNow : v7.totalCalls < limits.totalCalls := by omega
      have tapeNow : fs.next < steps := by omega
      cases lookup : lookupEntry v7 input with
      | some entry =>
        let v7Next := cachedSuccessor actor input entry v7
        let fsNext := (FSOracleExecution.query tape fs input).2
        have queryEq := cached_query_success_equation aligned limits actor input
          entry totalNow lookup
        have alignedNext : StateAligned tape finiteTape v7Next fsNext :=
          cached_successor_aligned aligned actor input entry lookup
        have totalNext : v7Next.totalCalls + remaining <= limits.totalCalls := by
          simp [v7Next, cachedSuccessor]
          omega
        have freshNext : v7Next.freshCalls + remaining <= limits.freshCalls := by
          simp [v7Next, cachedSuccessor]
          omega
        have tapeNext : fsNext.next + remaining <= steps := by
          have cache := lookup_some_implies_cache_some aligned input entry lookup
          simp [fsNext, FSOracleExecution.query, cache]
          omega
        have answerEq := cached_query_output aligned input entry lookup
        have inductiveStep :=
          ih entry.output v7Next fsNext alignedNext totalNext freshNext tapeNext
        simpa [compileScript, runMachine, queryEq, FSOracleExecution.run,
          answerEq, v7Next, fsNext] using inductiveStep
      | none =>
        let answer := tape fs.next
        let v7Next := freshSuccessor actor input answer v7
        let fsNext := (FSOracleExecution.query tape fs input).2
        have freshNow : v7.freshCalls < limits.freshCalls := by omega
        have queryEq := fresh_query_success_equation aligned limits actor input
          tapeNow totalNow freshNow lookup
        have alignedNext : StateAligned tape finiteTape v7Next fsNext :=
          fresh_successor_aligned aligned actor input tapeNow lookup
        have totalNext : v7Next.totalCalls + remaining <= limits.totalCalls := by
          simp [v7Next, freshSuccessor]
          omega
        have freshNext : v7Next.freshCalls + remaining <= limits.freshCalls := by
          simp [v7Next, freshSuccessor]
          omega
        have tapeNext : fsNext.next + remaining <= steps := by
          have cache := (lookup_none_iff_cache_none aligned input).mp lookup
          simp [fsNext, FSOracleExecution.query, cache]
          omega
        have answerEq := fresh_fs_query_output aligned input tapeNow lookup
        have inductiveStep :=
          ih answer v7Next fsNext alignedNext totalNext freshNext tapeNext
        simpa [compileScript, runMachine, queryEq, FSOracleExecution.run,
          answerEq, answer, v7Next, fsNext] using inductiveStep

#print axioms cached_query_success_equation
#print axioms run_compileScript_aligned

end AspisV8Completion.FSV8V7WholeScriptAlignment

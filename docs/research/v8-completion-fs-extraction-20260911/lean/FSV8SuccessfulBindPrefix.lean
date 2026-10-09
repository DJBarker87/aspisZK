import FSV8SuccessfulProgrammedAlignment
import FSV8CompileScriptAlgebra

/-!
# Successful compiled bind constructs its causal prefix

The full machine can have more fuel left than the continuation's static
bound when a padded/branching prefix executes fewer calls.  This theorem does
not invent an exact continuation-fuel equation.  It extracts only the
standalone prefix run and its aligned finite-script state, which is the causal
cut needed by the V8 challenge analysis.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000
set_option maxRecDepth 1800

namespace AspisV8Completion.FSV8SuccessfulBindPrefix

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73SharedOracleVerifierRunner
open FSV8V7OracleMachineBridge
open FSV8V7ProgrammedAlignment
open FSV8SuccessfulProgrammedAlignment
open FSV8CompileScriptAlgebra

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape

/-- Normal return of a compiled sequential composition constructs the actual
normally returned execution of its first Script and aligns that causal cut.
The conclusion is produced from the full return; prefix success is not an
input premise. -/
theorem returned_bind_constructs_prefix
    {A B : Type} {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps}
    (limits : OracleLimits) (actor : QueryActor) {m : Nat} :
    ∀ {n : Nat} (firstScript : Script Bytes Block A n)
      (next : A → Script Bytes Block B m)
      (v7 : OracleState) (fs : State Bytes Block)
      (result : B) (finalV7 : OracleState) (machineSteps : Nat),
      StateAligned tape finiteTape v7 fs →
      runMachine (controllerFromFreshAnswerTape finiteTape) limits actor (m+n)
          v7 (bindOracleMachine (compileScript firstScript)
            (fun value => compileScript (next value))) =
        { halt := .returned result, oracle := finalV7, steps := machineSteps } →
      ∃ prefixResult prefixV7 prefixSteps,
        runMachine (controllerFromFreshAnswerTape finiteTape) limits actor n v7
            (compileScript firstScript) =
          { halt := .returned prefixResult
            oracle := prefixV7
            steps := prefixSteps } ∧
        (run tape firstScript fs).1 = some prefixResult ∧
        StateAligned tape finiteTape prefixV7 (run tape firstScript fs).2 := by
  intro n firstScript
  induction firstScript with
  | done value =>
      intro next v7 fs result finalV7 machineSteps aligned returned
      exact ⟨value, v7, 0, by simp [compileScript, runMachine], rfl, aligned⟩
  | abort =>
      intro next v7 fs result finalV7 machineSteps aligned returned
      simp [compileScript, bindOracleMachine, runMachine] at returned
  | @ask remaining input continuation ih =>
      intro next v7 fs result finalV7 machineSteps aligned returned
      simp only [compileScript, bindOracleMachine, runMachine] at returned
      cases queried : queryOracle (controllerFromFreshAnswerTape finiteTape)
          limits actor v7 input with
      | error reason => simp [queried] at returned
      | ok outputAndState =>
          rcases outputAndState with ⟨output, nextV7⟩
          simp only [queried] at returned
          generalize tailEq :
              runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
                (m + remaining) nextV7
                (bindOracleMachine (compileScript (continuation output))
                  (fun value => compileScript (next value))) = tailRun
            at returned
          rcases tailRun with ⟨tailHalt, tailOracle, tailSteps⟩
          cases tailHalt with
          | oracleAbort reason => simp at returned
          | outOfFuel => simp at returned
          | returned tailResult =>
              simp only [MachineRun.mk.injEq, MachineHalt.returned.injEq]
                at returned
              rcases returned with ⟨rfl, rfl, stepsExact⟩
              have queryAligned := successful_query_aligned limits actor v7 fs
                aligned input output nextV7 queried
              obtain ⟨prefixResult, prefixV7, prefixSteps, prefixMachine,
                  prefixFunctional, prefixAligned⟩ :=
                ih output next nextV7
                  (FSOracleExecution.query tape fs input).2 tailResult tailOracle
                  tailSteps queryAligned.2 tailEq
              refine ⟨prefixResult, prefixV7, prefixSteps + 1, ?_, ?_, ?_⟩
              · simp only [compileScript, runMachine, queried]
                rw [prefixMachine]
              · simpa [FSOracleExecution.run, queryAligned.1] using
                  prefixFunctional
              · simpa [FSOracleExecution.run, queryAligned.1] using
                  prefixAligned

#print axioms returned_bind_constructs_prefix

end AspisV8Completion.FSV8SuccessfulBindPrefix

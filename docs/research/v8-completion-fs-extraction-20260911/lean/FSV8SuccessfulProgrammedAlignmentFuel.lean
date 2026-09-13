import FSV8SuccessfulProgrammedAlignment

/-!
# Success-local programmed alignment with excess machine fuel

`Script`'s index is an upper bound on oracle calls.  A surrounding compiled
machine can therefore run a script with more fuel than that index, especially
after a branch used fewer calls than its static allowance.  This leaf proves
the alignment result for precisely that situation.  It assumes only that the
actual machine returns.  No relation between the static Script index and the
supplied fuel is needed: normal return itself witnesses enough fuel along the
branch that actually executed.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000
set_option maxRecDepth 1800

namespace AspisV8Completion.FSV8SuccessfulProgrammedAlignmentFuel

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open FSV8V7OracleMachineBridge
open FSV8V7ProgrammedAlignment
open FSV8SuccessfulProgrammedAlignment

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape

/-- A normally returned compiled Script agrees with the finite interpreter
even when the executable machine was supplied excess fuel.  The theorem does
not assert that all supplied fuel was consumed. -/
theorem returned_compileScript_aligned_with_fuel
    {A : Type} {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps}
    (limits : OracleLimits) (actor : QueryActor) :
    ∀ {n : Nat} (script : Script Bytes Block A n)
      (fuel : Nat) (v7 : OracleState) (fs : State Bytes Block)
      (result : A) (finalV7 : OracleState) (machineSteps : Nat),
      StateAligned tape finiteTape v7 fs →
      runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
          (compileScript script) =
        { halt := .returned result, oracle := finalV7, steps := machineSteps } →
      (run tape script fs).1 = some result ∧
        StateAligned tape finiteTape finalV7 (run tape script fs).2 := by
  intro n script
  induction script with
  | done value =>
      intro fuel v7 fs result finalV7 machineSteps aligned returned
      simp only [compileScript, runMachine, MachineRun.mk.injEq,
        MachineHalt.returned.injEq] at returned
      rcases returned with ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, aligned⟩
  | abort =>
      intro fuel v7 fs result finalV7 machineSteps aligned returned
      simp [compileScript, runMachine] at returned
  | @ask remaining input next ih =>
      intro fuel v7 fs result finalV7 machineSteps aligned returned
      cases fuel with
      | zero =>
          simp [compileScript, runMachine] at returned
      | succ tailFuel =>
          simp only [compileScript, runMachine] at returned
          cases queried : queryOracle (controllerFromFreshAnswerTape finiteTape)
              limits actor v7 input with
          | error reason => simp [queried] at returned
          | ok outputAndState =>
              rcases outputAndState with ⟨output, nextV7⟩
              simp only [queried] at returned
              generalize tailEq :
                  runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
                    tailFuel nextV7 (compileScript (next output)) = tailRun
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
                  have tailAligned := ih output tailFuel nextV7
                    (FSOracleExecution.query tape fs input).2 tailResult tailOracle
                    tailSteps queryAligned.2 tailEq
                  constructor
                  · simpa [FSOracleExecution.run, queryAligned.1] using tailAligned.1
                  · simpa [FSOracleExecution.run, queryAligned.1] using tailAligned.2

#print axioms returned_compileScript_aligned_with_fuel

end AspisV8Completion.FSV8SuccessfulProgrammedAlignmentFuel

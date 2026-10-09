import AspisFormal.K1.V7FsAokExperiment
import AspisFormal.K1.V7Tag73SharedOracleVerifierRunner

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8ReturnedBindMachineSplit

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73SharedOracleVerifierRunner

/-! A success-only operational law for sequencing.  The fuel for the second
    run is the actual residual fuel left by the first run, rather than a
    syntactic budget or an assumed query count. -/
theorem runMachine_bind_returned_split
    {First Second : Type*}
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine First)
    (next : First → OracleMachine Second) (result : Second)
    (success :
      (runMachine controller limits actor fuel state
        (bindOracleMachine program next)).halt = .returned result) :
    ∃ value,
      let prefixRun := runMachine controller limits actor fuel state program
      let continuation := runMachine controller limits actor
        (fuel - prefixRun.steps) prefixRun.oracle (next value)
      prefixRun.halt = .returned value ∧
      continuation.halt = .returned result ∧
      (runMachine controller limits actor fuel state
        (bindOracleMachine program next)).oracle = continuation.oracle ∧
      (runMachine controller limits actor fuel state
        (bindOracleMachine program next)).steps =
        prefixRun.steps + continuation.steps := by
  induction fuel generalizing state program result with
  | zero =>
      cases program with
      | pure value =>
          exact ⟨value, by
            simpa [bindOracleMachine, runMachine] using success⟩
      | abort reason => simp [bindOracleMachine, runMachine] at success
      | query input continuation => simp [bindOracleMachine, runMachine] at success
  | succ fuel ih =>
      cases program with
      | pure value =>
          exact ⟨value, by
            simpa [bindOracleMachine, runMachine] using success⟩
      | abort reason => simp [bindOracleMachine, runMachine] at success
      | query input continuation =>
          cases queryResult : queryOracle controller limits actor state input with
          | error reason =>
              simp [bindOracleMachine, runMachine, queryResult] at success
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              simp only [bindOracleMachine, runMachine, queryResult] at success
              obtain ⟨value, prefixReturned, continuationReturned,
                oracleExact, stepsExact⟩ :=
                ih (state := nextState) (program := continuation output)
                  (result := result) success
              refine ⟨value, ?_⟩
              simp only [bindOracleMachine, runMachine, queryResult]
              have residualFuel :
                  (fuel + 1) -
                      ((runMachine controller limits actor fuel nextState
                        (continuation output)).steps + 1) =
                    fuel - (runMachine controller limits actor fuel nextState
                      (continuation output)).steps := by omega
              rw [residualFuel]
              exact ⟨prefixReturned, continuationReturned, oracleExact,
                by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                  using stepsExact⟩

#print axioms runMachine_bind_returned_split

end AspisV8Completion.FSV8ReturnedBindMachineSplit

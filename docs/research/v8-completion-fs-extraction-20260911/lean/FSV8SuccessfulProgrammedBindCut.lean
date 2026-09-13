import FSV8ReturnedBindMachineSplit
import FSV8SuccessfulProgrammedAlignmentFuel

/-!
# Successful programmed bind cut

This combines the operational bind decomposition with success-local
finite-tape alignment.  It exposes the actual causal prefix and continuation
of a normally returned compiled Script bind, including the real residual
machine fuel.  No worst-case room or unprogrammed-cache premise is assumed.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000
set_option maxRecDepth 1800

namespace AspisV8Completion.FSV8SuccessfulProgrammedBindCut

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73SharedOracleVerifierRunner
open FSV8V7OracleMachineBridge
open FSV8V7ProgrammedAlignment
open FSV8ReturnedBindMachineSplit
open FSV8SuccessfulProgrammedAlignmentFuel

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape

/-- Normal return of a compiled bind constructs its own returned prefix,
aligned finite-tape state at the cut, and returned continuation from that
state with the actual residual fuel. -/
theorem returned_bind_constructs_programmed_cut
    {A B : Type} {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps}
    (limits : OracleLimits) (actor : QueryActor)
    {n m fuel : Nat} (firstScript : Script Bytes Block A n)
    (next : A → Script Bytes Block B m)
    (v7 : OracleState) (fs : State Bytes Block)
    (result : B)
    (aligned : StateAligned tape finiteTape v7 fs)
    (success :
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
        (bindOracleMachine (compileScript firstScript)
          (fun value => compileScript (next value)))).halt = .returned result) :
    ∃ value,
      let prefixRun := runMachine (controllerFromFreshAnswerTape finiteTape)
        limits actor fuel v7 (compileScript firstScript)
      let continuationRun := runMachine
        (controllerFromFreshAnswerTape finiteTape) limits actor
        (fuel - prefixRun.steps) prefixRun.oracle
        (compileScript (next value))
      prefixRun.halt = .returned value ∧
      continuationRun.halt = .returned result ∧
      (run tape firstScript fs).1 = some value ∧
      StateAligned tape finiteTape prefixRun.oracle
        (run tape firstScript fs).2 ∧
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
        (bindOracleMachine (compileScript firstScript)
          (fun value => compileScript (next value)))).oracle =
        continuationRun.oracle ∧
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
        (bindOracleMachine (compileScript firstScript)
          (fun value => compileScript (next value)))).steps =
        prefixRun.steps + continuationRun.steps := by
  obtain ⟨value, prefixReturned, continuationReturned, finalOracle,
      totalSteps⟩ := runMachine_bind_returned_split
    (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
    (compileScript firstScript) (fun value => compileScript (next value))
    result success
  have prefixExact :
      runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
          (compileScript firstScript) =
        { halt := .returned value
          oracle := (runMachine (controllerFromFreshAnswerTape finiteTape)
            limits actor fuel v7 (compileScript firstScript)).oracle
          steps := (runMachine (controllerFromFreshAnswerTape finiteTape)
            limits actor fuel v7 (compileScript firstScript)).steps } := by
    generalize runEq : runMachine (controllerFromFreshAnswerTape finiteTape)
      limits actor fuel v7 (compileScript firstScript) = prefixRun
    rcases prefixRun with ⟨prefixHalt, prefixOracle, prefixSteps⟩
    simp only [runEq] at prefixReturned ⊢
    rw [prefixReturned]
  have prefixAligned := returned_compileScript_aligned_with_fuel limits actor
    firstScript fuel v7 fs value
    (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
      (compileScript firstScript)).oracle
    (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
      (compileScript firstScript)).steps
    aligned prefixExact
  exact ⟨value, prefixReturned, continuationReturned, prefixAligned.1,
    prefixAligned.2, finalOracle, totalSteps⟩

#print axioms returned_bind_constructs_programmed_cut

end AspisV8Completion.FSV8SuccessfulProgrammedBindCut

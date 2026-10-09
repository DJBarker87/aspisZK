import FSV8V7ProgrammedAlignment

/-!
# Success-local compiled-script alignment

This leaf removes the conservative static `+ n` room premises from the
existing structural compiler theorem.  Instead it conditions on the actual
compiled machine returning normally.  Every resource and fresh-tape fact is
therefore obtained from the realised successful query before the induction
continues.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000
set_option maxRecDepth 1800

namespace AspisV8Completion.FSV8SuccessfulProgrammedAlignment

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open FSV8V7OracleMachineBridge
open FSV8V7ProgrammedAlignment

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape

/-- One actually successful V7 query determines exactly the matching
finite-script answer and preserves the programmed-state alignment.  No
capacity for an unexecuted continuation is assumed. -/
theorem successful_query_aligned
    {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps}
    (limits : OracleLimits) (actor : QueryActor)
    (v7 : OracleState) (fs : State Bytes Block)
    (aligned : StateAligned tape finiteTape v7 fs)
    (input : Bytes) (output : Block) (nextV7 : OracleState)
    (success :
      queryOracle (controllerFromFreshAnswerTape finiteTape) limits actor
        v7 input = .ok (output, nextV7)) :
    (FSOracleExecution.query tape fs input).1 = output ∧
      StateAligned tape finiteTape nextV7
        (FSOracleExecution.query tape fs input).2 := by
  unfold queryOracle at success
  split at success
  next exhausted => contradiction
  next totalAvailable =>
    cases lookup : lookupEntry v7 input with
    | some entry =>
        simp only [lookup] at success
        cases success
        have cache := lookup_some_implies_cache_some aligned input entry lookup
        exact ⟨by simp [FSOracleExecution.query, cache],
          cached_successor_aligned aligned actor input entry lookup⟩
    | none =>
        simp only [lookup] at success
        split at success
        next exhausted => contradiction
        next freshAvailable =>
          cases answered : controllerFromFreshAnswerTape finiteTape v7.history input with
          | refuse => simp [answered] at success
          | answer controllerOutput =>
              simp only [answered, Except.ok.injEq, Prod.mk.injEq] at success
              rcases success with ⟨rfl, rfl⟩
              have exposure := controller_answer_implies_exposure_available
                finiteTape v7.history input controllerOutput answered
              have tapeAvailable : fs.next < steps := by
                rw [← aligned.freshCalls]
                rw [← aligned.coherent]
                exact exposure
              have controllerExact :=
                fresh_controller_answer aligned input tapeAvailable
              have outputExact : tape fs.next = controllerOutput :=
                ControllerDecision.answer.inj
                  (controllerExact.symm.trans answered)
              subst controllerOutput
              exact ⟨fresh_fs_query_output aligned input tapeAvailable lookup,
                fresh_successor_aligned aligned actor input tapeAvailable lookup⟩

/-- A normally returned compiled V7 machine run is the same successful
finite-script execution on the aligned tape, and its actual final oracle is
aligned with the finite interpreter's actual final state.  Unlike the older
forward theorem, this result has no worst-case total/fresh/tape room premise. -/
theorem returned_compileScript_aligned
    {A : Type} {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps}
    (limits : OracleLimits) (actor : QueryActor) :
    ∀ {n : Nat} (script : Script Bytes Block A n)
      (v7 : OracleState) (fs : State Bytes Block)
      (result : A) (finalV7 : OracleState) (machineSteps : Nat),
      StateAligned tape finiteTape v7 fs →
      runMachine (controllerFromFreshAnswerTape finiteTape) limits actor n v7
          (compileScript script) =
        { halt := .returned result, oracle := finalV7, steps := machineSteps } →
      (run tape script fs).1 = some result ∧
        StateAligned tape finiteTape finalV7 (run tape script fs).2 := by
  intro n script
  induction script with
  | done value =>
      intro v7 fs result finalV7 machineSteps aligned returned
      simp only [compileScript, runMachine, MachineRun.mk.injEq,
        MachineHalt.returned.injEq] at returned
      rcases returned with ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, aligned⟩
  | abort =>
      intro v7 fs result finalV7 machineSteps aligned returned
      simp [compileScript, runMachine] at returned
  | @ask remaining input next ih =>
      intro v7 fs result finalV7 machineSteps aligned returned
      simp only [compileScript, runMachine] at returned
      cases queried : queryOracle (controllerFromFreshAnswerTape finiteTape)
          limits actor v7 input with
      | error reason => simp [queried] at returned
      | ok outputAndState =>
          rcases outputAndState with ⟨output, nextV7⟩
          simp only [queried] at returned
          generalize tailEq :
              runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
                remaining nextV7 (compileScript (next output)) = tailRun
            at returned
          rcases tailRun with ⟨tailHalt, tailOracle, tailSteps⟩
          cases tailHalt with
          | oracleAbort reason => simp at returned
          | outOfFuel => simp at returned
          | returned tailResult =>
              simp only [MachineRun.mk.injEq, MachineHalt.returned.injEq] at returned
              rcases returned with ⟨rfl, rfl, stepsExact⟩
              have queryAligned := successful_query_aligned limits actor v7 fs
                aligned input output nextV7 queried
              have tailAligned := ih output nextV7
                (FSOracleExecution.query tape fs input).2 tailResult tailOracle
                tailSteps queryAligned.2 tailEq
              constructor
              · simpa [FSOracleExecution.run, queryAligned.1] using tailAligned.1
              · simpa [FSOracleExecution.run, queryAligned.1] using tailAligned.2

#print axioms successful_query_aligned
#print axioms returned_compileScript_aligned

end AspisV8Completion.FSV8SuccessfulProgrammedAlignment

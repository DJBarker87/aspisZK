import FSV8ReplayableSourceLaw

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8ReplayableSourceBindLaw
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open FSV8V7OracleMachineBridge FSV8V7WholeScriptUniformLaw
open FSV8V7PrehistoryContinuation
open FSV8V7CombinedPrehistoryLaw
open FSV8ReplayableSourceLaw
open ExtractionCollectorReplayableSource
open FSLiveSelectedMiddleQueryRho FSLiveLaterRelationSuffix

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Point := ExtractionCollectorReplayableSource.Point
abbrev Returned := ExtractionCollectorReplayableSource.Returned
abbrev FunctionalProducer := FSLiveSelectedMiddleQueryRho.FunctionalProducer
abbrev IncrementProducer := FSLiveLaterRelationSuffix.IncrementProducer

/-! A true sequential composition: the continuation is selected from the
 observation returned by the preprogram.  Non-returning preprograms do not
 start a verifier continuation. -/
def replayableBindCurrent (steps : Nat) (fallback : Block)
    (limits : OracleLimits) (actor : QueryActor) (preFuel : Nat)
    (preProgram : OracleMachine Observation) {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer) :
    FreshAnswerTape Block steps → CombinedOutcome Observation Returned :=
  fun finiteTape =>
    let pre := prehistoryRun steps limits actor preFuel preProgram finiteTape
    match pre.halt with
    | .returned observation =>
      let current := run (extendFreshTape finiteTape fallback)
        (replayableScript firstWork secondWork producer increment
          observation.body observation.initialDigest)
        (projectOracleState pre.oracle)
      { preHalt := pre.halt
        postHalt := some (currentHalt current.1)
        postState := current.2 }
    | _ =>
      { preHalt := pre.halt
        postHalt := none
        postState := projectOracleState pre.oracle }

def replayableBindV7 (steps : Nat) (fallback : Block)
    (limits : OracleLimits) (actor : QueryActor) (preFuel : Nat)
    (preProgram : OracleMachine Observation) {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer) :
    FreshAnswerTape Block steps → CombinedOutcome Observation Returned :=
  fun finiteTape =>
    let pre := prehistoryRun steps limits actor preFuel preProgram finiteTape
    match pre.halt with
    | .returned observation =>
      let continued := runMachine (controllerFromFreshAnswerTape finiteTape)
        limits actor (replayableCallBound n m) pre.oracle
        (compileScript (replayableScript firstWork secondWork producer increment
          observation.body observation.initialDigest))
      { preHalt := pre.halt
        postHalt := machineHalt continued.halt
        postState := projectOracleState continued.oracle }
    | _ =>
      { preHalt := pre.halt
        postHalt := none
        postState := projectOracleState pre.oracle }

theorem replayableBind_pointwise_eq
    {steps budget : Nat} (finiteTape : FreshAnswerTape Block steps) (fallback : Block)
    (limits : OracleLimits) (actor : QueryActor) (preFuel : Nat)
    (preProgram : OracleMachine Observation) {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer)
    (scriptFits : replayableCallBound n m ≤ budget)
    (totalRoom :
      (prehistoryRun steps limits actor preFuel preProgram finiteTape).oracle.totalCalls +
        budget ≤ limits.totalCalls)
    (freshRoom :
      (prehistoryRun steps limits actor preFuel preProgram finiteTape).oracle.freshCalls +
        budget ≤ limits.freshCalls)
    (tapeRoom :
      (projectOracleState
          (prehistoryRun steps limits actor preFuel preProgram finiteTape).oracle).next +
        budget ≤ steps) :
    replayableBindCurrent steps fallback limits actor preFuel preProgram
        firstWork secondWork producer increment finiteTape =
      replayableBindV7 steps fallback limits actor preFuel preProgram
        firstWork secondWork producer increment finiteTape := by
  let pre := prehistoryRun steps limits actor preFuel preProgram finiteTape
  cases h : pre.halt with
  | returned observation =>
      have exact := continue_from_uniform_prehistory_exact finiteTape fallback limits actor
        preFuel preProgram
        (replayableScript firstWork secondWork producer increment
          observation.body observation.initialDigest)
        (by dsimp [pre] at totalRoom ⊢; dsimp [replayableScript, replayableCallBound] at scriptFits; omega)
        (by dsimp [pre] at freshRoom ⊢; dsimp [replayableScript, replayableCallBound] at scriptFits; omega)
        (by dsimp [pre] at tapeRoom ⊢; dsimp [replayableScript, replayableCallBound] at scriptFits; omega)
      rcases exact with ⟨haltEq, stateEq⟩
      simp only [replayableBindCurrent, replayableBindV7]
      rw [h]
      dsimp
      congr 1
      · exact haltEq.symm
      · exact stateEq.symm
  | oracleAbort reason =>
      simp [replayableBindCurrent, replayableBindV7, pre, h]
  | outOfFuel =>
      simp [replayableBindCurrent, replayableBindV7, pre, h]

noncomputable def replayableBindCurrentLaw (steps : Nat) (fallback : Block)
    (limits : OracleLimits) (actor : QueryActor) (preFuel : Nat)
    (preProgram : OracleMachine Observation) {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer) :
    PMF (CombinedOutcome Observation Returned) :=
  (uniformDigestFreshTape steps).map
    (fun finiteTape => replayableBindCurrent steps fallback limits actor preFuel
      preProgram firstWork secondWork producer increment finiteTape)

noncomputable def replayableBindV7Law (steps : Nat) (fallback : Block)
    (limits : OracleLimits) (actor : QueryActor) (preFuel : Nat)
    (preProgram : OracleMachine Observation) {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer) :
    PMF (CombinedOutcome Observation Returned) :=
  (uniformDigestFreshTape steps).map
    (fun finiteTape => replayableBindV7 steps fallback limits actor preFuel
      preProgram firstWork secondWork producer increment finiteTape)

theorem replayableBind_current_law_eq_v7_law
    (steps budget : Nat) (fallback : Block)
    (limits : OracleLimits) (actor : QueryActor) (preFuel : Nat)
    (preProgram : OracleMachine Observation) {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer)
    (scriptFits : replayableCallBound n m ≤ budget)
    (rooms : ∀ finiteTape : FreshAnswerTape Block steps,
      (prehistoryRun steps limits actor preFuel preProgram finiteTape).oracle.totalCalls +
        budget ≤ limits.totalCalls ∧
      (prehistoryRun steps limits actor preFuel preProgram finiteTape).oracle.freshCalls +
        budget ≤ limits.freshCalls ∧
      (projectOracleState
          (prehistoryRun steps limits actor preFuel preProgram finiteTape).oracle).next +
        budget ≤ steps) :
    replayableBindCurrentLaw steps fallback limits actor preFuel preProgram
        firstWork secondWork producer increment =
      replayableBindV7Law steps fallback limits actor preFuel preProgram
        firstWork secondWork producer increment := by
  unfold replayableBindCurrentLaw replayableBindV7Law
  congr 1
  funext finiteTape
  exact replayableBind_pointwise_eq finiteTape fallback limits actor preFuel preProgram
    firstWork secondWork producer increment scriptFits
    (rooms finiteTape).1 (rooms finiteTape).2.1 (rooms finiteTape).2.2

#print axioms replayableBind_pointwise_eq
#print axioms replayableBind_current_law_eq_v7_law

end
end AspisV8Completion.FSV8ReplayableSourceBindLaw

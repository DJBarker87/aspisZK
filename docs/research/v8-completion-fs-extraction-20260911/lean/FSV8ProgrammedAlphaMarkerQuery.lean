import FSV8ProgrammedAlphaCutWitness
import AspisFormal.K1.V7Tag73AtomicPairReplay

/-!
# The programmed alpha marker is one actual oracle query

This small operational leaf exposes the literal marker input, returned answer,
and successor oracle of a successful marker-continuation machine.  A caller
with `ProgrammedAlphaCutWitness` supplies its already-recorded successful
marker run.  No freshness or probability claim is made here.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000

namespace AspisV8Completion.FSV8ProgrammedAlphaMarkerQuery

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73OperationalOracleExposure
open FSV8V7OracleMachineBridge
open FSV8PostOODGammaScript
open FSLiveSourceFunctionalMiddle
open FSLiveSelectedMiddleQueryRho
open FSV8ExecutablePreAlphaFactorization
open FSV8BeforeAlphaMarkerFactorization

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev K := FSNonzeroQM31.K

/-- A successful compiled marker continuation consists of its one literal
oracle call followed by a pure return.  Consequently its returned digest and
final oracle are exactly the query answer and successor state. -/
theorem returned_marker_continuation_exposes_query
    {steps : Nat}
    (finiteTape : FreshAnswerTape Block steps)
    (limits : OracleLimits) (actor : QueryActor)
    (out : FSV8PostOODGammaScript.OODResult) (gamma : K)
    (body : Bytes) (z : Fin 10 → K)
    (boundary : PreAlpha out gamma body z) (preDigest : Block)
    (before : BeforeAlphaMarker out gamma body z)
    (markerFuel : Nat) (markerState : OracleState)
    (returned :
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
        markerFuel markerState
        (compileScript
          (alphaMarkerContinuation out gamma body z before))).halt =
        .returned (Except.ok boundary, preDigest)) :
    ∃ nextState,
      queryOracle (controllerFromFreshAnswerTape finiteTape) limits actor
        markerState
        (List.ofFn before.digest ++ [0, 20] ++
          (0 :: alpha0NonceBytes body)) =
          .ok (boundary.digest, nextState) ∧
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
        markerFuel markerState
        (compileScript
          (alphaMarkerContinuation out gamma body z before))).oracle =
        nextState := by
  have compiledMarker :
      compileScript (alphaMarkerContinuation out gamma body z before) =
        .query
          (List.ofFn before.digest ++ [0, 20] ++
            (0 :: alpha0NonceBytes body))
          (fun answer => .pure
            ((Except.ok
              { kappa := before.kappa
                tau := before.tau
                functional := before.functional
                functionalRun := before.functionalRun
                digest := answer } :
                Except FSLiveSourceFunctionalMiddle.Error
                  (PreAlpha out gamma body z)),
              answer)) := by
    rfl
  have returnedQuery :
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
        markerFuel markerState
        (.query
          (List.ofFn before.digest ++ [0, 20] ++
            (0 :: alpha0NonceBytes body))
          (fun answer => .pure
            ((Except.ok
              { kappa := before.kappa
                tau := before.tau
                functional := before.functional
                functionalRun := before.functionalRun
                digest := answer } :
                Except FSLiveSourceFunctionalMiddle.Error
                  (PreAlpha out gamma body z)),
              answer)))).halt =
        .returned
          ((Except.ok boundary : Except FSLiveSourceFunctionalMiddle.Error
            (PreAlpha out gamma body z)), preDigest) := by
    rw [← compiledMarker]
    exact returned
  obtain ⟨answer, nextState, querySuccess⟩ :=
    run_machine_returned_query_exposes_first_call
      (controllerFromFreshAnswerTape finiteTape) limits actor markerFuel
      markerState
      (List.ofFn before.digest ++ [0, 20] ++
        (0 :: alpha0NonceBytes body))
      (fun answer => .pure
        ((Except.ok
          { kappa := before.kappa
            tau := before.tau
            functional := before.functional
            functionalRun := before.functionalRun
            digest := answer } :
            Except FSLiveSourceFunctionalMiddle.Error
              (PreAlpha out gamma body z)),
          answer))
      ((Except.ok boundary : Except FSLiveSourceFunctionalMiddle.Error
        (PreAlpha out gamma body z)), preDigest) returnedQuery
  have exactReturned := returnedQuery
  cases markerFuel with
  | zero => simp [runMachine] at exactReturned
  | succ remainingFuel =>
      simp only [runMachine, querySuccess] at exactReturned
      have resultExact := MachineHalt.returned.inj exactReturned
      have outcomeExact := congrArg Prod.fst resultExact
      have boundaryExact := Except.ok.inj outcomeExact
      have answerExact : answer = boundary.digest := by
        exact congrArg PreAlpha.digest boundaryExact
      subst answer
      refine ⟨nextState, querySuccess, ?_⟩
      rw [compiledMarker]
      simp only [runMachine, querySuccess]

#print axioms returned_marker_continuation_exposes_query

end
end AspisV8Completion.FSV8ProgrammedAlphaMarkerQuery

import FSV8ProgrammedWholeAlphaCut
import FSV8AlphaTargetDisposition
import FSV8ReturnedBindMachineSplit
import FSV8ActualAlphaAtomicPairInputs

/-!
# Programmed alpha cut exposes the actual candidate and target disposition

This leaf connects the accepted whole-run cut to the first alpha candidate
query.  It inverts the successful `postAlphaScript` machine bind at the
actual residual oracle and fuel, rather than classifying an independently
supplied transcript.  The resulting literal candidate input is then totally
classified relative to the oracle state frozen before verifier execution.

No probability, freshness, restoration success, or extraction claim is made.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 2400

namespace AspisV8Completion.FSV8ProgrammedAlphaCandidateDisposition

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73AtomicPairReplay
open FSV8V7OracleMachineBridge
open FSV8PostOODGammaScript
open FSLiveSourceFunctionalMiddle
open FSV8ExecutablePreAlphaFactorization
open FSV8ProgrammedWholeAlphaCut
open FSV8AlphaChallengeInputBridge
open FSV8AlphaTargetDisposition
open FSV8ReturnedBindMachineSplit
open FSV8ActualAlphaAtomicPairInputs

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K

def NoPriorAdversaryInput (state : OracleState) (input : ShaInput) : Prop :=
  ¬ ∃ record, record ∈ freezeAdversaryQ1 state ∧ record.input = input

/-- Causal classification at both relevant cuts.  The final two constructors
separate a target inserted by the verifier prefix from one genuinely absent
when the candidate call begins. -/
inductive CausalAlphaDisposition
    (rootState candidateState : OracleState) (input : ShaInput) : Prop where
  | priorAdversary
      (record : QueryRecord)
      (member : record ∈ freezeAdversaryQ1 rootState)
      (inputEq : record.input = input)
  | priorTarget
      (noAdversary : NoPriorAdversaryInput rootState input)
      (entry : TableEntry)
      (lookup : lookupEntry rootState input = some entry)
  | introducedDuringVerifier
      (noAdversary : NoPriorAdversaryInput rootState input)
      (rootAbsent : lookupEntry rootState input = none)
      (entry : TableEntry)
      (candidateLookup : lookupEntry candidateState input = some entry)
  | freshAtCandidate
      (noAdversary : NoPriorAdversaryInput rootState input)
      (rootAbsent : lookupEntry rootState input = none)
      (candidateAbsent : lookupEntry candidateState input = none)

noncomputable def causal_alpha_disposition
    (rootState candidateState : OracleState) (input : ShaInput) :
    CausalAlphaDisposition rootState candidateState input := by
  classical
  by_cases q1 : ∃ record,
      record ∈ freezeAdversaryQ1 rootState ∧ record.input = input
  · exact .priorAdversary (Classical.choose q1)
      (Classical.choose_spec q1).1 (Classical.choose_spec q1).2
  · cases rootLookup : lookupEntry rootState input with
    | some entry => exact .priorTarget q1 entry rootLookup
    | none =>
        cases candidateLookup : lookupEntry candidateState input with
        | some entry =>
            exact .introducedDuringVerifier q1 rootLookup entry candidateLookup
        | none => exact .freshAtCandidate q1 rootLookup candidateLookup

def sourceMachineRun
    {steps : Nat} (finiteTape : FreshAnswerTape Block steps)
    (limits : OracleLimits) (actor : QueryActor)
    {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (digest : Block) (v7 : OracleState) (fuel : Nat) :=
  runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
    (compileScript (sourceThenGammaScript firstWork secondWork body digest))

def preAlphaMachineRun
    {steps : Nat} (finiteTape : FreshAnswerTape Block steps)
    (limits : OracleLimits) (actor : QueryActor)
    {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (digest : Block) (v7 : OracleState) (fuel : Nat)
    (out : FSV7OODBodyScript.Result) (gamma : K) (z : Fin 10 → K)
    (sourceDigest : Block) :=
  let sourceRun := sourceMachineRun finiteTape limits actor firstWork secondWork
    body digest v7 fuel
  runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
    (fuel - sourceRun.steps) sourceRun.oracle
    (compileScript (preAlphaScript out gamma body z sourceDigest))

def alphaCandidateMachineRun
    {steps : Nat} (finiteTape : FreshAnswerTape Block steps)
    (limits : OracleLimits) (actor : QueryActor)
    {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (digest : Block) (v7 : OracleState) (fuel : Nat)
    (out : FSV7OODBodyScript.Result) (gamma : K) (z : Fin 10 → K)
    (sourceDigest : Block) (boundary : PreAlpha out gamma body z) :=
  let sourceRun := sourceMachineRun finiteTape limits actor firstWork secondWork
    body digest v7 fuel
  let preRun := preAlphaMachineRun finiteTape limits actor firstWork secondWork
    body digest v7 fuel out gamma z sourceDigest
  runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
    ((fuel - sourceRun.steps) - preRun.steps) preRun.oracle
    (compileScript (FSNonzeroQM31.candidateScript boundary.digest))

/-- Source-shaped evidence for the exact first alpha candidate of a successful
programmed cut.  The source and pre-alpha returns prevent the candidate run
from being attached to an unrelated body or oracle state. -/
def ProgrammedAlphaCandidateDisposition
    {steps : Nat}
    (finiteTape : FreshAnswerTape Block steps)
    (limits : OracleLimits) (actor : QueryActor)
    {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (body : Bytes) (digest : Block)
    (v7 : OracleState) (fuel : Nat) : Prop :=
  ∃ out : FSV7OODBodyScript.Result, ∃ gamma : K, ∃ sourceDigest : Block,
    ∃ boundary : PreAlpha out gamma body z, ∃ prefixDigest : Block,
    ∃ alpha0 : K, ∃ candidateDigest : Block, ∃ candidateOutput : ShaOutput,
    ∃ candidateNextState : OracleState, ∃ candidateOrigin : AnswerOrigin,
    (sourceMachineRun finiteTape limits actor firstWork secondWork body digest
      v7 fuel).halt = .returned (.ok (out, gamma), sourceDigest) ∧
    (preAlphaMachineRun finiteTape limits actor firstWork secondWork body digest
      v7 fuel out gamma z sourceDigest).halt =
        .returned (.ok boundary, prefixDigest) ∧
    (alphaCandidateMachineRun finiteTape limits actor firstWork secondWork body
      digest v7 fuel out gamma z sourceDigest boundary).halt =
        .returned (.ok alpha0, candidateDigest) ∧
    FSV8GammaChallengeInputBridge.firstScriptInput
      (FSNonzeroQM31.candidateScript boundary.digest) =
      some (List.ofFn boundary.digest ++ [1]) ∧
    queryOracle (controllerFromFreshAnswerTape finiteTape) limits actor
      (preAlphaMachineRun finiteTape limits actor firstWork secondWork body
        digest v7 fuel out gamma z sourceDigest).oracle
      (List.ofFn boundary.digest ++ [1]) =
        .ok (candidateOutput, candidateNextState) ∧
    candidateNextState.history =
      (preAlphaMachineRun finiteTape limits actor firstWork secondWork body
        digest v7 fuel out gamma z sourceDigest).oracle.history ++
      [{ input := List.ofFn boundary.digest ++ [1]
         output := candidateOutput
         actor := actor
         origin := candidateOrigin }] ∧
    CausalAlphaDisposition v7
      (preAlphaMachineRun finiteTape limits actor firstWork secondWork body
        digest v7 fuel out gamma z sourceDigest).oracle
      (List.ofFn boundary.digest ++ [1])

/-- The actual successful post-alpha continuation constructs its first
candidate return and an exhaustive disposition for that exact query input. -/
theorem programmed_alpha_cut_constructs_candidate_disposition
    {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps}
    (limits : OracleLimits) (actor : QueryActor)
    {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (body : Bytes) (digest : Block)
    (v7 : OracleState) (fs : State Bytes Block) (fuel : Nat)
    (cut : ProgrammedAlphaCut (tape := tape) finiteTape limits actor firstWork
      secondWork z body digest v7 fs fuel) :
    ProgrammedAlphaCandidateDisposition finiteTape limits actor firstWork
      secondWork z body digest v7 fuel := by
  unfold ProgrammedAlphaCut at cut
  rcases cut with ⟨out, gamma, sourceDigest, boundary, prefixDigest, before,
    middle, middleDigest, sourceReturned, _sourceFunctional, preAlphaReturned,
    _markerReturned, _markerContinuationReturned, postAlphaReturned,
    _markerFunctional, _markerAligned, _markerContinuationFunctional,
    _afterMarkerAligned⟩
  let sourceRun := sourceMachineRun finiteTape limits actor firstWork secondWork
    body digest v7 fuel
  let preRun := preAlphaMachineRun finiteTape limits actor firstWork secondWork
    body digest v7 fuel out gamma z sourceDigest
  let alphaNext :
      (Except FSNonzeroQM31.Error K × Block) →
        Script Bytes Block (Result out gamma body z × Block) 217 :=
    fun alphaDraw =>
      match alphaDraw.1 with
      | .error e => .done
          (Except.error (Error.alpha0 e), alphaDraw.2)
      | .ok alpha0 =>
          bind (m := 0) (FSLiveQueryRhoSuffix.queryRhoScript body
            alphaDraw.2) fun suffixDraw =>
            .done (match suffixDraw.1 with
              | .error e => (Except.error (Error.suffix e), suffixDraw.2)
              | .ok (queries, rho) =>
                let selectedMiddle := FSLiveSelectedMiddleQueryRho.Success.mk
                  boundary.kappa boundary.tau alpha0 queries rho
                let sourceSuccess : Success out gamma body z :=
                  { middle := selectedMiddle
                    functional := boundary.functional
                    functionalRun := boundary.functionalRun }
                (Except.ok sourceSuccess, suffixDraw.2))
  have compiledPostAlpha :
      compileScript (postAlphaScript out gamma body z boundary) =
        bindOracleMachine
          (compileScript (FSNonzeroQM31.candidateScript boundary.digest))
          (fun value => compileScript (alphaNext value)) := by
    unfold postAlphaScript
    rw [FSV8CompileScriptAlgebra.compileScript_bind]
    apply congrArg
      (bindOracleMachine
        (compileScript (FSNonzeroQM31.candidateScript boundary.digest)))
    funext value
    rcases value with ⟨outcome, returnedDigest⟩
    cases outcome <;> rfl
  have postAlphaBindReturned :
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
        ((fuel - sourceRun.steps) - preRun.steps) preRun.oracle
        (bindOracleMachine
          (compileScript (FSNonzeroQM31.candidateScript boundary.digest))
          (fun value => compileScript (alphaNext value)))).halt =
          .returned (.ok middle, middleDigest) := by
    rw [← compiledPostAlpha]
    simpa [sourceRun, preRun, sourceMachineRun, preAlphaMachineRun] using
      postAlphaReturned
  obtain ⟨candidateValue, candidateReturned, continuationReturned,
      _finalOracle, _totalSteps⟩ :=
    runMachine_bind_returned_split
      (controllerFromFreshAnswerTape finiteTape) limits actor
      ((fuel - sourceRun.steps) - preRun.steps) preRun.oracle
      (compileScript (FSNonzeroQM31.candidateScript boundary.digest))
      (fun value => compileScript (alphaNext value))
      (.ok middle, middleDigest) postAlphaBindReturned
  rcases candidateValue with ⟨candidateOutcome, candidateDigest⟩
  cases candidateOutcome with
  | error e =>
      simp [alphaNext, compileScript, runMachine] at continuationReturned
  | ok alpha0 =>
      let afterAlphaNonce : Transcript :=
        { digest := boundary.digest, oracle := FSFirstFresh.empty }
      obtain ⟨next, compiledCandidate⟩ :=
        compiled_alpha_candidate_starts_with_atomic_pair afterAlphaNonce
      have firstQueryReturnedRaw :
          (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
            ((fuel - sourceRun.steps) - preRun.steps) preRun.oracle
            (.query (alphaAtomicPairInputs afterAlphaNonce).1 (fun output =>
              .query (alphaAtomicPairInputs afterAlphaNonce).2
                (next output)))).halt =
              .returned (.ok alpha0, candidateDigest) := by
        rw [← compiledCandidate]
        exact candidateReturned
      have firstQueryReturned :
          (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
            ((fuel - sourceRun.steps) - preRun.steps) preRun.oracle
            (.query (List.ofFn boundary.digest ++ [1]) (fun output =>
              .query (List.ofFn boundary.digest ++ [2])
                (next output)))).halt =
              .returned (.ok alpha0, candidateDigest) := by
        simpa [afterAlphaNonce, alphaAtomicPairInputs] using
          firstQueryReturnedRaw
      obtain ⟨candidateOutput, candidateNextState, candidateQuery⟩ :=
        run_machine_returned_query_exposes_first_call
          (controllerFromFreshAnswerTape finiteTape) limits actor
          ((fuel - sourceRun.steps) - preRun.steps) preRun.oracle
          (List.ofFn boundary.digest ++ [1])
          (fun output => .query (List.ofFn boundary.digest ++ [2])
            (next output))
          (.ok alpha0, candidateDigest) firstQueryReturned
      obtain ⟨candidateOrigin, candidateHistory⟩ :=
        query_oracle_success_appends_one_record
          (controllerFromFreshAnswerTape finiteTape) limits actor preRun.oracle
          candidateNextState (List.ofFn boundary.digest ++ [1])
          candidateOutput candidateQuery
      have causalDisposition := causal_alpha_disposition v7 preRun.oracle
        (List.ofFn boundary.digest ++ [1])
      refine ⟨out, gamma, sourceDigest, boundary, prefixDigest, alpha0,
        candidateDigest, candidateOutput, candidateNextState, candidateOrigin,
        ?_, ?_, ?_,
        FSV8GammaChallengeInputBridge.candidateScript_first_input
          boundary.digest,
        ?_, ?_, ?_⟩
      · simpa [sourceRun, sourceMachineRun] using sourceReturned
      · simpa [preRun, preAlphaMachineRun, sourceMachineRun] using
          preAlphaReturned
      · simpa [alphaCandidateMachineRun, sourceRun, preRun,
          sourceMachineRun, preAlphaMachineRun] using candidateReturned
      · simpa [preRun] using candidateQuery
      · simpa [preRun] using candidateHistory
      · simpa [preRun] using causalDisposition

#print axioms programmed_alpha_cut_constructs_candidate_disposition
#print axioms ProgrammedAlphaCandidateDisposition
#print axioms causal_alpha_disposition

end
end AspisV8Completion.FSV8ProgrammedAlphaCandidateDisposition

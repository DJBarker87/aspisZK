import ExtractionCollectorSource
import FSAuthenticatedInterleavedPrefixMiddle
import FSV8V7OracleMachineBridge

/-!
# Verify the body returned by a legal replay

The earlier replayable-source shell fixed a completed proof body in the
experiment observation.  That is useful for deterministic transcript checks,
but it is not the replay interface required by a Fiat--Shamir extractor: after
a programmed challenge, the same-tape adversary may return a different proof
body.

This leaf runs a verifier program on the value actually returned by each legal
replay and starts it from that replay's resulting shared-oracle state.  The
selected specialization tags every verifier result with its input body and
proves that a checked result refers to exactly the replay-returned body.

It does not assert that a replay succeeds, that the selected verifier accepts,
or that accepted records form a complete extraction matrix.  The adversary
black box, alpha-boundary configuration and probability of collecting all
cells remain separate obligations.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 1200

namespace AspisV8Completion.ExtractionCollectorVerifiedBodySource

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open ExtractionCollectorSource
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSAuthenticatedInterleavedPrefixMiddle
open FSV8V7OracleMachineBridge

noncomputable section

/-- A verifier whose oracle calls run after one legal adversary replay. -/
structure ReplayVerifier
    (Submitted VerifierResult Record RejectReason ResourceReason : Type*) where
  start : Submitted → OracleMachine VerifierResult
  check : VerifierResult → SourceCheckOutcome Record RejectReason ResourceReason

/-- All failure classes remain visible.  In particular, an oracle abort or
fuel exhaustion in the verifier is not converted to a rejected proof or a
checked record. -/
inductive VerifiedAttemptOutcome
    (Submitted Record RejectReason ResourceReason : Type*) where
  | replayFailure (reason : CouplingFailure)
  | verifierAbort (reason : OracleAbort)
  | verifierTimeout
  | rejected (reason : RejectReason)
  | resource (reason : ResourceReason)
  | checked (submitted : Submitted) (record : Record)

/-- Execute the verifier on the exact value returned by a legal same-tape
replay, from the replay's final shared-oracle state. -/
def verifiedSourceAttempt
    {TapeIdentity Observation Statement Proof Submitted VerifierResult Record
      RejectReason ResourceReason : Type*}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Submitted)
    (configuration : OriginReplayConfiguration)
    (verifier : ReplayVerifier Submitted VerifierResult Record
      RejectReason ResourceReason)
    (controller : AdaptiveController) (limits : OracleLimits) (fuel : Nat) :
    VerifiedAttemptOutcome Submitted Record RejectReason ResourceReason :=
  match constructLegalReplay origin.capability
      (fixedFirstRunRecordFromOrigin origin configuration) with
  | .error reason => .replayFailure reason
  | .ok replay =>
      let verifierRun := runMachine controller limits .verifier fuel
        replay.val.replayRun.oracle (verifier.start replay.val.returned)
      match verifierRun.halt with
      | .oracleAbort reason => .verifierAbort reason
      | .outOfFuel => .verifierTimeout
      | .returned result =>
          match verifier.check result with
          | .accepted record => .checked replay.val.returned record
          | .rejected reason => .rejected reason
          | .resource reason => .resource reason

/-- A checked outcome is constructed from one operational replay and an
actual verifier return.  Neither the submitted value nor the checked record
is a caller-selected substitute. -/
theorem verifiedSourceAttempt_checked
    {TapeIdentity Observation Statement Proof Submitted VerifierResult Record
      RejectReason ResourceReason : Type*}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Submitted)
    (configuration : OriginReplayConfiguration)
    (verifier : ReplayVerifier Submitted VerifierResult Record
      RejectReason ResourceReason)
    (controller : AdaptiveController) (limits : OracleLimits) (fuel : Nat)
    (submitted : Submitted) (record : Record)
    (success : verifiedSourceAttempt origin configuration verifier controller
      limits fuel = .checked submitted record) :
    ∃ replay : {run : CoupledReplay TapeIdentity Statement Proof Submitted //
        IsOperationalCoupling origin.capability
          (fixedFirstRunRecordFromOrigin origin configuration) run},
      constructLegalReplay origin.capability
          (fixedFirstRunRecordFromOrigin origin configuration) = .ok replay ∧
      replay.val.returned = submitted ∧
      ∃ verifierResult,
        (runMachine controller limits .verifier fuel replay.val.replayRun.oracle
          (verifier.start replay.val.returned)).halt =
            .returned verifierResult ∧
        verifier.check verifierResult = .accepted record := by
  unfold verifiedSourceAttempt at success
  cases replayed : constructLegalReplay origin.capability
      (fixedFirstRunRecordFromOrigin origin configuration) with
  | error reason => simp [replayed] at success
  | ok replay =>
      simp only [replayed] at success
      cases runEq : runMachine controller limits .verifier fuel
          replay.val.replayRun.oracle (verifier.start replay.val.returned) with
      | mk halt oracle steps =>
        cases halt with
        | oracleAbort reason => simp [runEq] at success
        | outOfFuel => simp [runEq] at success
        | returned verifierResult =>
            simp only [runEq] at success
            cases checked : verifier.check verifierResult with
            | rejected reason => simp [checked] at success
            | resource reason => simp [checked] at success
            | accepted found =>
                simp [checked] at success
                rcases success with ⟨rfl, rfl⟩
                exact ⟨replay, rfl, rfl, verifierResult, by simp [runEq], checked⟩

/-! ## The selected staged verifier, tagged by its input body -/

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K

/-- Fixed result type for a body-indexed selected verifier execution. -/
structure SelectedVerifierResult (z : Fin 10 → K) where
  body : Bytes
  output : Except FSAuthenticatedInterleavedPrefixMiddle.Error
      (FSAuthenticatedInterleavedPrefixMiddle.Record body z) × Block

/-- The accepted projection retains the dependent record and final digest. -/
structure SelectedAccepted (z : Fin 10 → K) where
  body : Bytes
  record : FSAuthenticatedInterleavedPrefixMiddle.Record body z
  finalDigest : Block

inductive SelectedReject where
  | source (error : FSAuthenticatedInterleavedPrefixMiddle.Error)
  deriving DecidableEq

abbrev SelectedResource := Empty

def mapMachine {A B : Type*} (f : A → B) : OracleMachine A → OracleMachine B
  | .pure value => .pure (f value)
  | .abort reason => .abort reason
  | .query input next => .query input (fun answer => mapMachine f (next answer))

theorem runMachine_map_returned {A B : Type*}
    (f : A → B) (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) : ∀ fuel state program value,
    (runMachine controller limits actor fuel state (mapMachine f program)).halt =
      .returned value →
    ∃ original,
      (runMachine controller limits actor fuel state program).halt =
        .returned original ∧ value = f original := by
  intro fuel
  induction fuel with
  | zero =>
      intro state program value success
      cases program with
      | pure original =>
          simp [mapMachine, runMachine] at success
          exact ⟨original, rfl, success.symm⟩
      | abort reason => simp [mapMachine, runMachine] at success
      | query input next => simp [mapMachine, runMachine] at success
  | succ fuel ih =>
      intro state program value success
      cases program with
      | pure original =>
          exact ⟨original, rfl, by simpa [mapMachine, runMachine] using success.symm⟩
      | abort reason => simp [mapMachine, runMachine] at success
      | query input next =>
          simp only [mapMachine, runMachine] at success
          cases queried : queryOracle controller limits actor state input with
          | error reason => simp [queried] at success
          | ok pair =>
              rcases pair with ⟨answer, nextState⟩
              simp only [queried] at success
              obtain ⟨original, returned, exactValue⟩ :=
                ih nextState (next answer) value success
              refine ⟨original, ?_, exactValue⟩
              simp only [runMachine, queried]
              exact returned

def selectedVerifierStart {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (cuts : RootCuts) (initialDigest : Block)
    (body : Bytes) : OracleMachine (SelectedVerifierResult z) :=
  mapMachine (fun output => SelectedVerifierResult.mk body output)
    (compileScript
      (wholeStagedScript firstWork secondWork z cuts body initialDigest))

def selectedCheck {z : Fin 10 → K} (result : SelectedVerifierResult z) :
    SourceCheckOutcome (SelectedAccepted z) SelectedReject SelectedResource :=
  match result.output.1 with
  | .error error => .rejected (.source error)
  | .ok record => .accepted
      { body := result.body
        record := record
        finalDigest := result.output.2 }

def selectedReplayVerifier {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (cuts : RootCuts) (initialDigest : Block) :
    ReplayVerifier Bytes (SelectedVerifierResult z) (SelectedAccepted z)
      SelectedReject SelectedResource where
  start := selectedVerifierStart firstWork secondWork z cuts initialDigest
  check := selectedCheck

theorem selectedVerifierStart_returned_body {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (cuts : RootCuts) (initialDigest : Block)
    (body : Bytes) (controller : AdaptiveController) (limits : OracleLimits)
    (fuel : Nat) (state : OracleState) (result : SelectedVerifierResult z)
    (success : (runMachine controller limits .verifier fuel state
      (selectedVerifierStart firstWork secondWork z cuts initialDigest body)).halt =
        .returned result) :
    result.body = body := by
  obtain ⟨original, _run, exactResult⟩ := runMachine_map_returned
    (fun output => SelectedVerifierResult.mk body output)
    controller limits .verifier fuel state
    (compileScript
      (wholeStagedScript firstWork secondWork z cuts body initialDigest))
    result success
  rw [exactResult]

/-- The tagged result also exposes the underlying successful execution of the
unmodified functional staged script on that body. -/
theorem selectedVerifierStart_constructs_functional_run {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (cuts : RootCuts) (initialDigest : Block)
    (body : Bytes) (controller : AdaptiveController) (limits : OracleLimits)
    (fuel : Nat) (state : OracleState) (result : SelectedVerifierResult z)
    (success : (runMachine controller limits .verifier fuel state
      (selectedVerifierStart firstWork secondWork z cuts initialDigest body)).halt =
        .returned result) :
    ∃ output,
      (runMachine controller limits .verifier fuel state
        (compileScript
          (wholeStagedScript firstWork secondWork z cuts body initialDigest))).halt =
            .returned output ∧
      result = SelectedVerifierResult.mk body output := by
  obtain ⟨output, functionalRun, exactResult⟩ := runMachine_map_returned
    (fun returned => SelectedVerifierResult.mk body returned)
    controller limits .verifier fuel state
    (compileScript
      (wholeStagedScript firstWork secondWork z cuts body initialDigest))
    result success
  exact ⟨output, functionalRun, exactResult⟩

theorem selectedCheck_accepted_body {z : Fin 10 → K}
    (result : SelectedVerifierResult z) (accepted : SelectedAccepted z)
    (success : selectedCheck result = .accepted accepted) :
    accepted.body = result.body := by
  unfold selectedCheck at success
  cases output : result.output.1 with
  | error error => simp [output] at success
  | ok record =>
      simp only [output] at success
      have same : SelectedAccepted.mk result.body record result.output.2 = accepted :=
        SourceCheckOutcome.accepted.inj success
      exact (congrArg SelectedAccepted.body same).symm

/-- A checked selected-verifier replay is tied to the exact body returned by
the adversary replay.  This is the same-body property missing from a checker
that receives an independently supplied semantic program. -/
theorem selected_attempt_checked_same_body
    {TapeIdentity Observation Statement Proof : Type*} {n m : Nat}
    (origin : SameTapeExperimentOrigin TapeIdentity Observation Statement Proof Bytes)
    (configuration : OriginReplayConfiguration)
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (cuts : RootCuts) (initialDigest : Block)
    (controller : AdaptiveController) (limits : OracleLimits) (fuel : Nat)
    (submitted : Bytes) (accepted : SelectedAccepted z)
    (success : verifiedSourceAttempt origin configuration
      (selectedReplayVerifier firstWork secondWork z cuts initialDigest)
      controller limits fuel = .checked submitted accepted) :
    accepted.body = submitted := by
  obtain ⟨replay, _replayed, returned, verifierResult, verifierRun, checked⟩ :=
    verifiedSourceAttempt_checked origin configuration
      (selectedReplayVerifier firstWork secondWork z cuts initialDigest)
      controller limits fuel submitted accepted success
  have verifierBody := selectedVerifierStart_returned_body firstWork secondWork z
    cuts initialDigest replay.val.returned controller limits fuel
    replay.val.replayRun.oracle verifierResult verifierRun
  have acceptedBody := selectedCheck_accepted_body verifierResult accepted checked
  exact acceptedBody.trans (verifierBody.trans returned)

/-- Full one-attempt provenance: one operational same-tape adversary replay
returns the submitted bytes, and the functional staged script then returns
normally on those exact bytes from the replay-final oracle.  The selected
checker accepts that tagged return.  This is not the later relation terminal
or payment validator. -/
theorem selected_attempt_checked_constructs_functional_run
    {TapeIdentity Observation Statement Proof : Type*} {n m : Nat}
    (origin : SameTapeExperimentOrigin TapeIdentity Observation Statement Proof Bytes)
    (configuration : OriginReplayConfiguration)
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (cuts : RootCuts) (initialDigest : Block)
    (controller : AdaptiveController) (limits : OracleLimits) (fuel : Nat)
    (submitted : Bytes) (accepted : SelectedAccepted z)
    (success : verifiedSourceAttempt origin configuration
      (selectedReplayVerifier firstWork secondWork z cuts initialDigest)
      controller limits fuel = .checked submitted accepted) :
    ∃ replay : {run : CoupledReplay TapeIdentity Statement Proof Bytes //
        IsOperationalCoupling origin.capability
          (fixedFirstRunRecordFromOrigin origin configuration) run},
      constructLegalReplay origin.capability
          (fixedFirstRunRecordFromOrigin origin configuration) = .ok replay ∧
      replay.val.returned = submitted ∧
      ∃ output,
        (runMachine controller limits .verifier fuel replay.val.replayRun.oracle
          (compileScript (wholeStagedScript firstWork secondWork z cuts
            replay.val.returned initialDigest))).halt = .returned output ∧
        selectedCheck (SelectedVerifierResult.mk replay.val.returned output) =
          .accepted accepted ∧
        accepted.body = submitted := by
  obtain ⟨replay, replayed, returned, verifierResult, verifierRun, checked⟩ :=
    verifiedSourceAttempt_checked origin configuration
      (selectedReplayVerifier firstWork secondWork z cuts initialDigest)
      controller limits fuel submitted accepted success
  obtain ⟨output, functionalRun, exactResult⟩ :=
    selectedVerifierStart_constructs_functional_run firstWork secondWork z cuts
      initialDigest replay.val.returned controller limits fuel
      replay.val.replayRun.oracle verifierResult verifierRun
  have exactCheck :
      selectedCheck (SelectedVerifierResult.mk replay.val.returned output) =
        .accepted accepted := by
    rw [← exactResult]
    exact checked
  exact ⟨replay, replayed, returned, output, functionalRun, exactCheck,
    selected_attempt_checked_same_body origin configuration firstWork secondWork
      z cuts initialDigest controller limits fuel submitted accepted success⟩

#print axioms verifiedSourceAttempt_checked
#print axioms runMachine_map_returned
#print axioms selectedVerifierStart_returned_body
#print axioms selectedVerifierStart_constructs_functional_run
#print axioms selectedCheck_accepted_body
#print axioms selected_attempt_checked_same_body
#print axioms selected_attempt_checked_constructs_functional_run

end
end AspisV8Completion.ExtractionCollectorVerifiedBodySource

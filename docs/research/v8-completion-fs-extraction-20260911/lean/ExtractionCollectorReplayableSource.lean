import ExtractionCollectorSource
import FSLiveLaterRelationSuffix
import FSV8V7WholeScriptAlignment

/-!
# Replayable same-execution collector source through later relation coins

This replaces the collector's `.pure` source at the strongest currently
source-shaped boundary.  The black box executes the actual bounded
source/OOD/gamma, repaired middle/query/rho and response1--response3 `Script`.
A successful return contains the same submitted body and all sampled relation
coins produced by that execution; none is supplied as a checker label.

This does not attach a `SameBodyRelation.Result`.  The authenticated query
increment arithmetic, causal relation strategy/ordinary scalar and terminal
checker remain explicit producer seams.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.ExtractionCollectorReplayableSource

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment AspisK1.V7FsStateRestorationCoupling
open ExtractionCollectorSource
open FSV8PostOODGammaScript FSLiveSelectedMiddleQueryRho
open FSLiveLaterRelationSuffix
open FSV8V7OracleMachineBridge

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Point := FSV7OODBodyScript.Point
abbrev OODResult := FSV7OODBodyScript.Result
abbrev K := FSNonzeroQM31.K
abbrev PrefixError := Sum FSOODSampler.Error FSNonzeroQM31.Error

noncomputable section

inductive Error where
  | prefix (error : PrefixError)
  | middle (error : FSLiveSelectedMiddleQueryRho.Error)
  | later (error : FSLiveLaterRelationSuffix.Error)
  deriving DecidableEq

/-- Every field is produced by one chronological execution.  `body` is the
literal input used for all proof-carried byte ranges. -/
structure Record where
  body : Bytes
  ood : OODResult
  gamma : K
  middle : FSLiveSelectedMiddleQueryRho.Success
  later : FSLiveLaterRelationSuffix.Success

def Record.alpha0 (record : Record) : K := record.middle.alpha0
def Record.coins (record : Record) : Fin 3 -> K := record.later.coins

abbrev Returned := Except Error Record × Block

/-- Unlike `sourceMiddleQueryRhoScript`, prefix sampler errors are returned
for the checker to classify.  Actual `Script.abort` from canonical/source work
still propagates through `bind` and is compiled as controller refusal. -/
def replayableScript {n m : Nat}
    (firstWork : Point -> Script Bytes Block Unit n)
    (secondWork : Point -> Point -> Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer)
    (body : Bytes) (digest : Block) :=
  FSTranscriptScript.bind
      (sourceThenGammaScript firstWork secondWork body digest) fun prefixDraw =>
    match prefixDraw.1 with
    | .error e => .done (Except.error (Error.prefix e), prefixDraw.2)
    | .ok (out, gamma) =>
      FSTranscriptScript.bind
        (middleQueryRhoScript producer out gamma body prefixDraw.2)
        fun middleDraw =>
          match middleDraw.1 with
          | .error e => .done (Except.error (Error.middle e), middleDraw.2)
          | .ok middle =>
            FSTranscriptScript.bind (m := 0)
                (laterScript increment out gamma middle body middleDraw.2)
              fun laterDraw =>
                .done (match laterDraw.1 with
                  | .error e => (Except.error (Error.later e), laterDraw.2)
                  | .ok later =>
                    (Except.ok (Record.mk body out gamma middle later), laterDraw.2))

structure Observation where
  body : Bytes
  initialDigest : Block

/-- Fixed source code is closed over the black box, not varied by replay
configuration.  The only hidden tape token needed by this deterministic
program constructor is `PUnit`; oracle answers remain controlled by the V7
same-tape execution machinery. -/
def replayableBlackBox {n m : Nat}
    (firstWork : Point -> Script Bytes Block Unit n)
    (secondWork : Point -> Point -> Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer) :
    SameTapeBlackBox Unit Observation Returned where
  start _ observation :=
    compileScript (replayableScript firstWork secondWork producer increment
      observation.body observation.initialDigest)

theorem replayable_start_is_compiled_script {n m : Nat}
    (firstWork : Point -> Script Bytes Block Unit n)
    (secondWork : Point -> Point -> Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer)
    (observation : Observation) :
    (replayableBlackBox firstWork secondWork producer increment).start () observation =
      compileScript (replayableScript firstWork secondWork producer increment
        observation.body observation.initialDigest) := by
  rfl

def makeReplayableOrigin {n m : Nat} {TapeIdentity Statement Proof : Type*}
    (firstWork : Point -> Script Bytes Block Unit n)
    (secondWork : Point -> Point -> Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer)
    (identity : TapeIdentity)
    (observation : Observation) (controller : AdaptiveController)
    (limits : OracleLimits) (fuel : Nat) (initialOracle : OracleState)
    (forgeryOf : Returned -> Option (PublicProof Statement Proof)) :
    SameTapeExperimentOrigin TapeIdentity Observation Statement Proof Returned :=
  makeSourceOrigin (replayableBlackBox firstWork secondWork producer increment) ()
    identity observation controller limits fuel initialOracle forgeryOf

/-- The origin handed to `sourceAttempt` starts the compiled chronological
script, unlike the previous `.pure (consume ...)` origin. -/
theorem replayable_origin_start {n m : Nat}
    {TapeIdentity Statement Proof : Type*}
    (firstWork : Point -> Script Bytes Block Unit n)
    (secondWork : Point -> Point -> Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer)
    (identity : TapeIdentity)
    (observation : Observation) (controller : AdaptiveController)
    (limits : OracleLimits) (fuel : Nat) (initialOracle : OracleState)
    (forgeryOf : Returned -> Option (PublicProof Statement Proof)) :
    (makeReplayableOrigin firstWork secondWork producer increment identity observation
      controller limits fuel initialOracle forgeryOf).capability.start observation =
      compileScript (replayableScript firstWork secondWork producer increment
        observation.body observation.initialDigest) := by
  rfl

inductive RejectReason where
  | source (error : Error)
  deriving DecidableEq

abbrev ResourceReason := Empty

/-- The checker can only expose a record actually returned by the replay. -/
def checkReturned (returned : Returned) :
    SourceCheckOutcome Record RejectReason ResourceReason :=
  match returned.1 with
  | .error e => .rejected (.source e)
  | .ok record => .accepted record

def checker : ActualResultChecker Returned Record RejectReason ResourceReason where
  check := checkReturned

theorem checkReturned_accepted (returned : Returned) (record : Record)
    (accepted : checkReturned returned = .accepted record) :
    returned.1 = .ok record := by
  cases result : returned.1 with
  | error e => simp [checkReturned, result] at accepted
  | ok actual =>
    have same : actual = record := by
      simpa [checkReturned, result] using accepted
    exact congrArg Except.ok same

/-- A successful current interpreter run decomposes at the actual gamma pause
and the actual middle pause.  This establishes same-execution provenance of
body/gamma/alpha0 without a `Progress` or successful-fork premise. -/
theorem successful_run_components {n m : Nat}
    (firstWork : Point -> Script Bytes Block Unit n)
    (secondWork : Point -> Point -> Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer)
    (body : Bytes) (digest : Block)
    (tape : Tape) (oracle : FSBoundedTranscript.Oracle)
    (record : Record) (finalDigest : Block)
    (success :
      (run tape (replayableScript firstWork secondWork producer increment body digest)
        oracle).1 = some (.ok record, finalDigest)) :
    exists out gamma prefixDigest middle middleDigest later,
      (run tape (sourceThenGammaScript firstWork secondWork body digest) oracle).1 =
        some (.ok (out, gamma), prefixDigest) /\
      (run tape (middleQueryRhoScript producer out gamma body prefixDigest)
        (run tape (sourceThenGammaScript firstWork secondWork body digest) oracle).2).1 =
        some (.ok middle, middleDigest) /\
      (run tape (laterScript increment out gamma middle body middleDigest)
        (run tape (middleQueryRhoScript producer out gamma body prefixDigest)
          (run tape (sourceThenGammaScript firstWork secondWork body digest)
            oracle).2).2).1 = some (.ok later, finalDigest) /\
      record = Record.mk body out gamma middle later := by
  unfold replayableScript at success
  rw [run_bind] at success
  cases prefixRun :
      (run tape (sourceThenGammaScript firstWork secondWork body digest) oracle).1 with
  | none => simp [prefixRun] at success
  | some prefixValue =>
    rcases prefixValue with ⟨prefixResult, prefixDigest⟩
    cases prefixResult with
    | error e => simp [prefixRun, run] at success
    | ok pair =>
      rcases pair with ⟨out, gamma⟩
      simp only [prefixRun] at success
      rw [run_bind] at success
      cases middleRun :
          (run tape (middleQueryRhoScript producer out gamma body prefixDigest)
            (run tape (sourceThenGammaScript firstWork secondWork body digest)
              oracle).2).1 with
      | none => simp [middleRun] at success
      | some middleValue =>
        rcases middleValue with ⟨middleResult, middleDigest⟩
        cases middleResult with
        | error e => simp [middleRun, run] at success
        | ok middle =>
          simp only [middleRun] at success
          rw [run_bind] at success
          cases laterRun :
              (run tape (laterScript increment out gamma middle body middleDigest)
                (run tape (middleQueryRhoScript producer out gamma body prefixDigest)
                  (run tape (sourceThenGammaScript firstWork secondWork body digest)
                    oracle).2).2).1 with
          | none => simp [laterRun] at success
          | some laterValue =>
            rcases laterValue with ⟨laterResult, laterDigest⟩
            cases laterResult with
            | error e => simp [laterRun, run] at success
            | ok later =>
              simp [laterRun, run] at success
              rcases success with ⟨rfl, rfl⟩
              exact ⟨out, gamma, prefixDigest, middle, middleDigest, later,
                rfl, middleRun, laterRun, rfl⟩

/-- The accepted collector labels are projections of the actual returned
record; no caller-supplied gamma/alpha labelling functions are needed. -/
theorem accepted_labels_are_returned (returned : Returned) (record : Record)
    (accepted : checkReturned returned = .accepted record) :
    returned.1 = .ok record /\
      record.gamma = record.gamma /\ record.alpha0 = record.middle.alpha0 := by
  exact ⟨checkReturned_accepted returned record accepted, rfl, rfl⟩

/-- The collector's later coins are the live suffix outputs carried by the
same returned record, not labels selected after replay. -/
theorem accepted_later_coins_are_returned (returned : Returned) (record : Record)
    (accepted : checkReturned returned = .accepted record) :
    returned.1 = .ok record /\
      record.coins 0 = record.later.alpha1 /\
      record.coins 1 = record.later.alpha2 /\
      record.coins 2 = record.later.alpha3 := by
  exact ⟨checkReturned_accepted returned record accepted,
    record.later.coins_literal⟩

#print axioms replayable_start_is_compiled_script
#print axioms replayable_origin_start
#print axioms checkReturned_accepted
#print axioms successful_run_components
#print axioms accepted_labels_are_returned
#print axioms accepted_later_coins_are_returned

end
end AspisV8Completion.ExtractionCollectorReplayableSource

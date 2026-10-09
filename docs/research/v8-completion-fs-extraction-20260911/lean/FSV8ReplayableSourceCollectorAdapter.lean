import FSV8ReplayableSourceBindLaw
import ExtractionCollectorSource

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8ReplayableSourceCollectorAdapter
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open ExtractionCollectorSource ExtractionCollectorReplayableSource
open FSV8ReplayableSourceBindLaw
open FSV8V7OracleMachineBridge
open FSLiveSelectedMiddleQueryRho FSLiveLaterRelationSuffix

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Point := ExtractionCollectorReplayableSource.Point
abbrev Returned := ExtractionCollectorReplayableSource.Returned
abbrev FunctionalProducer := FSLiveSelectedMiddleQueryRho.FunctionalProducer
abbrev IncrementProducer := FSLiveLaterRelationSuffix.IncrementProducer

/-! OracleMachine bind is the source-side causal bridge: a preprogram must
return an Observation before the replayable verifier program is constructed.
Abort and resource behavior of the preprogram remain part of the machine. -/
def bindMachine {A B : Type} : OracleMachine A → (A → OracleMachine B) → OracleMachine B
  | .pure value, continuation => continuation value
  | .query input next, continuation =>
      .query input (fun output => bindMachine (next output) continuation)
  | .abort reason, _ => .abort reason

def bindReplayableBlackBox {n m : Nat}
    (preProgram : OracleMachine Observation)
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer) :
    SameTapeBlackBox Unit Observation Returned where
  start _ observation :=
    bindMachine preProgram (fun produced =>
      compileScript (replayableScript firstWork secondWork producer increment
        produced.body produced.initialDigest))

def bindReplayableOrigin {n m : Nat}
    (preProgram : OracleMachine Observation)
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer)
    {TapeIdentity Statement Proof : Type*}
    (identity : TapeIdentity) (seed : Observation)
    (controller : AdaptiveController) (limits : OracleLimits) (fuel : Nat)
    (initialOracle : OracleState)
    (forgeryOf : Returned → Option (PublicProof Statement Proof)) :
    SameTapeExperimentOrigin TapeIdentity Observation Statement Proof Returned :=
  makeSourceOrigin
    (bindReplayableBlackBox preProgram firstWork secondWork producer increment)
    () identity seed controller limits fuel initialOracle forgeryOf

def bindReplayableSourceAttempt {n m : Nat}
    (preProgram : OracleMachine Observation)
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer)
    {TapeIdentity Statement Proof : Type*}
    (identity : TapeIdentity) (seed : Observation)
    (controller : AdaptiveController) (limits : OracleLimits) (fuel : Nat)
    (initialOracle : OracleState)
    (forgeryOf : Returned → Option (PublicProof Statement Proof))
    (configuration : OriginReplayConfiguration)
    (checker : ActualResultChecker Returned Record
      ExtractionCollectorReplayableSource.Error Empty) :
    AttemptOutcome Record ExtractionCollectorReplayableSource.Error Empty :=
  sourceAttempt
    (bindReplayableOrigin preProgram firstWork secondWork producer increment
      identity seed controller limits fuel initialOracle forgeryOf)
    configuration checker

theorem bindReplayableOrigin_start {n m : Nat}
    (preProgram : OracleMachine Observation)
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer)
    {TapeIdentity Statement Proof : Type*}
    (identity : TapeIdentity) (seed : Observation)
    (controller : AdaptiveController) (limits : OracleLimits) (fuel : Nat)
    (initialOracle : OracleState)
    (forgeryOf : Returned → Option (PublicProof Statement Proof)) :
    (bindReplayableOrigin preProgram firstWork secondWork producer increment
      identity seed controller limits fuel initialOracle forgeryOf).capability.start seed =
      bindMachine preProgram (fun produced =>
        compileScript (replayableScript firstWork secondWork producer increment
          produced.body produced.initialDigest)) := by
  rfl

theorem bindReplayableOrigin_first_execution {n m : Nat}
    (preProgram : OracleMachine Observation)
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer)
    {TapeIdentity Statement Proof : Type*}
    (identity : TapeIdentity) (seed : Observation)
    (controller : AdaptiveController) (limits : OracleLimits) (fuel : Nat)
    (initialOracle : OracleState)
    (forgeryOf : Returned → Option (PublicProof Statement Proof)) :
    (bindReplayableOrigin preProgram firstWork secondWork producer increment
      identity seed controller limits fuel initialOracle forgeryOf).firstExecution =
      runMachine controller limits .adversary fuel initialOracle
        (bindMachine preProgram (fun produced =>
          compileScript (replayableScript firstWork secondWork producer increment
            produced.body produced.initialDigest))) := by
  rfl

theorem bindReplayableSourceAttempt_is_actual_sourceAttempt {n m : Nat}
    (preProgram : OracleMachine Observation)
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer)
    {TapeIdentity Statement Proof : Type*}
    (identity : TapeIdentity) (seed : Observation)
    (controller : AdaptiveController) (limits : OracleLimits) (fuel : Nat)
    (initialOracle : OracleState)
    (forgeryOf : Returned → Option (PublicProof Statement Proof))
    (configuration : OriginReplayConfiguration)
    (checker : ActualResultChecker Returned Record
      ExtractionCollectorReplayableSource.Error Empty) :
    bindReplayableSourceAttempt preProgram firstWork secondWork producer increment
      identity seed controller limits fuel initialOracle forgeryOf configuration checker =
      sourceAttempt
        (bindReplayableOrigin preProgram firstWork secondWork producer increment
          identity seed controller limits fuel initialOracle forgeryOf)
        configuration checker := by
  rfl

#print axioms bindReplayableOrigin_start
#print axioms bindReplayableOrigin_first_execution
#print axioms bindReplayableSourceAttempt_is_actual_sourceAttempt

end
end AspisV8Completion.FSV8ReplayableSourceCollectorAdapter

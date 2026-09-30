import V7ProductionSnapshotObserverR28ToR26Prechallenge
import V7CallerCurrentReleaseR30InitialFoldSixSource
import V7CallerCurrentReleaseR30CircleAccumulator

/-!
# Production chain reaches the source-bound initial fold

The original production-tail witness retained only the generic prechallenge
call.  This bridge follows the same accepted chain through the concrete
circle accumulator and preserves the exact log-ten fold that supplies it.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace AspisV7ProductionSnapshotObserverR30InitialFoldSource

open Aeneas Aeneas.Std Result ControlFlow Error
open V7ProductionSnapshotObserverR28
open AspisV7ProductionSnapshotObserverR28SourceBridge
open AspisV7ProductionSnapshotObserverR28ToR26Prechallenge
open V7CallerCurrentReleaseR26
open V7CallerCurrentReleaseR26AcceptedInnerDispatch
open V7CallerCurrentReleaseR26AcceptedInnerToPrechallenge
open V7CallerCurrentReleaseR26WeightFoldLoopTrace
open V7CallerCurrentReleaseR30OuterAccumulator
open V7CallerCurrentReleaseR30CircleAccumulator
open V7CallerCurrentReleaseR30InitialPrechallengeDispatch
open V7CallerCurrentReleaseR30InitialFoldSixSource

/-- The concrete accepted production chain, including the source trace of the
initial six-component fold. -/
def ReachesCurrentInitialFold
    (hash : HashFn) (wire : Wire)
    (context : V7CallerCurrentReleaseR26.v6_transcript.V6TranscriptContext)
    (hidingContext : HidingContext)
    (inactiveRowGroups : Array Std.U8 64#usize)
    (inactiveGroupMasks : Slice Std.U16) (checkPow : Bool)
    (statement : Statement) (queryFold : QueryFold)
    (transcript : Transcript)
    (snapshot : AspisV7ProductionSnapshotObserverR28SourceBridge.Snapshot) :
    Prop :=
  Nonempty (Σ inner : AcceptedInnerDispatch terminalInst queryFoldInst
      prechallengeInst hash wire context hidingContext inactiveRowGroups
      inactiveGroupMasks checkPow statement queryFold () true transcript
      (some snapshot),
    Σ chain : AcceptedInnerPrechallengeChain inner,
    Σ prepared : AcceptedPreparedAccumulator chain.outer,
    Σ accumulator : AcceptedCircleAccumulator prepared,
    Σ dispatch : AcceptedInitialPrechallengeDispatch accumulator.origin,
    Σ trace : FirstDeferredFoldTrace accumulator.origin.state.2.2.2.2
      dispatch.initialFold.alpha dispatch.initialFold.weights,
    InitialFoldSixSourceTrace accumulator.origin.state.2.2.2.2
      dispatch.initialFold.alpha dispatch.initialFold.weights trace
      prepared.mScale0 prepared.mScale1 prepared.mScale2 prepared.mPoint0
      prepared.mPoint1 prepared.mPoint2 prepared.rowGroups prepared.groupMasks
      (alloc.vec.Vec.new field.QM31) accumulator.step0.scale
      accumulator.step1.scale accumulator.step0.factors accumulator.step1.factors)

/-- Every accepted R28 production prechallenge chain reaches the exact
source-bound initial fold in the current verifier. -/
theorem reaches_r26_prechallenge_reaches_current_initial_fold
    (hash : HashFn) (wire : Wire)
    (context : V7CallerCurrentReleaseR26.v6_transcript.V6TranscriptContext)
    (hidingContext : HidingContext)
    (inactiveRowGroups : Array Std.U8 64#usize)
    (inactiveGroupMasks : Slice Std.U16) (checkPow : Bool)
    (statement : Statement) (queryFold : QueryFold)
    (transcript : Transcript)
    (snapshot : AspisV7ProductionSnapshotObserverR28SourceBridge.Snapshot)
    (reaches : ReachesR26Prechallenge hash wire context hidingContext
      inactiveRowGroups inactiveGroupMasks checkPow statement queryFold
      transcript snapshot) :
    ReachesCurrentInitialFold hash wire context hidingContext inactiveRowGroups
      inactiveGroupMasks checkPow statement queryFold transcript snapshot := by
  rcases reaches with ⟨⟨inner, chain⟩⟩
  obtain ⟨prepared⟩ :=
    V7CallerCurrentReleaseR30OuterAccumulator.AcceptedOnefoldLoopDispatch.exposesPreparedAccumulator
      chain.outer
  obtain ⟨accumulator⟩ :=
    V7CallerCurrentReleaseR30CircleAccumulator.AcceptedPreparedAccumulator.exposesCircleAccumulator
      prepared
  obtain ⟨dispatch⟩ :=
    V7CallerCurrentReleaseR30InitialPrechallengeDispatch.AcceptedCircleBodyOrigin.exposesInitialPrechallengeDispatch
      accumulator.origin
  obtain ⟨trace⟩ := first_deferred_fold_exposes_exact_trace
    dispatch.initialFold.foldRun
  obtain ⟨source, _⟩ := initial_fold_exposes_six_source_components
    accumulator.origin.state.2.2.2.2 dispatch.initialFold.alpha
    dispatch.initialFold.weights trace prepared.mScale0 prepared.mScale1
    prepared.mScale2 prepared.mPoint0 prepared.mPoint1 prepared.mPoint2
    prepared.rowGroups prepared.groupMasks (alloc.vec.Vec.new field.QM31)
    accumulator.step0.scale accumulator.step1.scale accumulator.step0.factors
    accumulator.step1.factors accumulator.componentsExact
  exact ⟨⟨inner, chain, prepared, accumulator, dispatch, trace, source⟩⟩

#print axioms reaches_r26_prechallenge_reaches_current_initial_fold

end AspisV7ProductionSnapshotObserverR30InitialFoldSource

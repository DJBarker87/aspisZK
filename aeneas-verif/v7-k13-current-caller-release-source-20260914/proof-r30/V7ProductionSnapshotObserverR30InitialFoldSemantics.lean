import V7ProductionSnapshotObserverR30InitialFoldSource
import V7CallerCurrentReleaseR30InitialFoldSixSemantics
import V7CallerCurrentReleaseR30StatementPointsCanonical
import V7ProductionSnapshotObserverR30InitialClaimCanonical
import V7CallerCurrentReleaseR30CircleArithmeticCanonical
import V7CallerCurrentReleaseR30CircleFactorsTerminalBridge

/-!
# Canonical initial-fold accumulator from the production chain

This turns the concrete production initial-fold trace into the exact
canonical log-eight accumulator consumed by query insertion.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace AspisV7ProductionSnapshotObserverR30InitialFoldSemantics

open Aeneas Aeneas.Std Result ControlFlow Error
open V7ProductionSnapshotObserverR28
open AspisV7ProductionSnapshotObserverR28SourceBridge
open AspisV7ProductionSnapshotObserverR28ToR26Prechallenge
open AspisV7ProductionSnapshotObserverR30InitialFoldSource
open V7CallerCurrentReleaseR26
open V7CallerCurrentReleaseR26AcceptedInnerDispatch
open V7CallerCurrentReleaseR26AcceptedInnerToPrechallenge
open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26MultilinearFoldSemantics
open V7CallerCurrentReleaseR26TensorFoldSemantics
open V7CallerCurrentReleaseR30OuterAccumulator
open V7CallerCurrentReleaseR30CircleAccumulator
open V7CallerCurrentReleaseR30InitialPrechallengeDispatch
open V7CallerCurrentReleaseR30InitialFoldSixSemantics
open V7CallerCurrentReleaseR30StatementPointsCanonical
open V7CallerCurrentReleaseR30SemanticPointCanonical
open V7ProductionSnapshotObserverR30InitialClaimCanonical
open V7CallerCurrentReleaseR30CircleArithmeticCanonical
open V7CallerCurrentReleaseR30CircleFactorsTerminalBridge

abbrev RawQM31 := field.QM31

private theorem scale_read_canonical
    (scales : Array RawQM31 3#usize) (index : Std.Usize) (value : RawQM31)
    (canonical : CanonicalPointScales scales)
    (run : Array.index_usize scales index = ok value) :
    GeneratedCanonicalQM31 value := by
  unfold Array.index_usize at run
  split at run
  · cases run
  · rename_i present
    have presentList : scales.val[index.val]? = some value := by
      simpa [Result.ok.inj run] using present
    have bound : index.val < scales.val.length := by
      by_contra outOfBounds
      have absent : scales.val[index.val]? = none :=
        List.getElem?_eq_none (by omega)
      rw [absent] at presentList
      cases presentList
    have valueExact : value = scales.val[index.val]! := by
      symm
      exact List.getElem!_of_getElem? presentList
    rw [valueExact]
    exact canonical index.val (by simpa [Array.length_eq] using bound)

private theorem vector_point_canonical
    (point : Array RawQM31 10#usize) (vector : alloc.vec.Vec RawQM31)
    (vectorExact : vector.val = point.val)
    (canonical : ∀ index (bound : index < point.val.length),
      GeneratedCanonicalQM31 (point.val[index]'bound)) :
    V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
      vector.val := by
  rw [vectorExact]
  intro value member
  obtain ⟨index, indexBound, indexExact⟩ := List.getElem_of_mem member
  rw [← indexExact]
  simpa only [getElem!_pos] using canonical index indexBound

private theorem vector_point_length
    (point : Array RawQM31 10#usize) (vector : alloc.vec.Vec RawQM31)
    (vectorExact : vector.val = point.val) : vector.val.length = 10 := by
  rw [vectorExact]
  exact point.property

private theorem vector_exact_at
    (points : Array (Array RawQM31 10#usize) 3#usize)
    (vector : alloc.vec.Vec RawQM31) (row : Nat)
    (rowBound : row < points.val.length)
    (vectorExact : vector.val = points.val[row]!.val) :
    vector.val = (points.val[row]'rowBound).val := by
  calc
    vector.val = points.val[row]!.val := vectorExact
    _ = (points.val[row]'rowBound).val :=
      congrArg Subtype.val (getElem!_pos points.val row rowBound)

private theorem cast_ten_u32_to_usize :
    (UScalar.cast .Usize (10#u32)).val = 10 := by
  rw [UScalar.cast_val_eq, Nat.mod_eq_of_lt]
  rw [UScalar.ofNatCore_val_eq]
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    norm_num [UScalarTy.numBits, hbits]

/-- The concrete production chain reaches a source-bound initial fold whose
six returned cells meet every canonicality and dimension condition expected by
the established terminal relation theorem. -/
def ReachesCurrentInitialFoldSemantics
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
    Σ trace : V7CallerCurrentReleaseR26WeightFoldLoopTrace.FirstDeferredFoldTrace
      accumulator.origin.state.2.2.2.2 dispatch.initialFold.alpha
      dispatch.initialFold.weights,
    InitialFoldSixSemantics accumulator.origin.state.2.2.2.2
      dispatch.initialFold.alpha dispatch.initialFold.weights trace
      prepared.mScale0 prepared.mScale1 prepared.mScale2 prepared.mPoint0
      prepared.mPoint1 prepared.mPoint2 prepared.rowGroups prepared.groupMasks
      (alloc.vec.Vec.new field.QM31) accumulator.step0.scale
      accumulator.step1.scale accumulator.step0.factors accumulator.step1.factors)

theorem reaches_r26_prechallenge_reaches_current_initial_fold_semantics
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
    ReachesCurrentInitialFoldSemantics hash wire context hidingContext
      inactiveRowGroups inactiveGroupMasks checkPow statement queryFold
      transcript snapshot := by
  obtain ⟨inner, chain, prepared, accumulator, dispatch, trace, _source⟩ :=
    Classical.choice
      (reaches_r26_prechallenge_reaches_current_initial_fold hash wire context
        hidingContext inactiveRowGroups inactiveGroupMasks checkPow statement
        queryFold transcript snapshot reaches)
  have pointScalesCanonical := accepted_production_point_scales_canonical chain
  have pointsCanonical := accepted_production_statement_points_canonical chain
  have mScale0Canonical := scale_read_canonical chain.outer.pointScales 0#usize
    prepared.mScale0 pointScalesCanonical prepared.scale0Run
  have mScale1Canonical := scale_read_canonical chain.outer.pointScales 1#usize
    prepared.mScale1 pointScalesCanonical prepared.scale1Run
  have mScale2Canonical := scale_read_canonical chain.outer.pointScales 2#usize
    prepared.mScale2 pointScalesCanonical prepared.scale2Run
  have row0Bound : 0 < chain.outer.points.val.length := by simp
  have row1Bound : 1 < chain.outer.points.val.length := by simp
  have row2Bound : 2 < chain.outer.points.val.length := by simp
  let point0 := chain.outer.points.val[0]'row0Bound
  let point1 := chain.outer.points.val[1]'row1Bound
  let point2 := chain.outer.points.val[2]'row2Bound
  have point0Exact := vector_exact_at chain.outer.points prepared.mPoint0 0
    row0Bound prepared.point0Exact
  have point1Exact := vector_exact_at chain.outer.points prepared.mPoint1 1
    row1Bound prepared.point1Exact
  have point2Exact := vector_exact_at chain.outer.points prepared.mPoint2 2
    row2Bound prepared.point2Exact
  have point0Canonical : ∀ index (bound : index < point0.val.length),
      GeneratedCanonicalQM31 (point0.val[index]'bound) := by
    intro index bound
    exact canonical_points_entry chain.outer.points pointsCanonical 0 index row0Bound bound
  have point1Canonical : ∀ index (bound : index < point1.val.length),
      GeneratedCanonicalQM31 (point1.val[index]'bound) := by
    intro index bound
    exact canonical_points_entry chain.outer.points pointsCanonical 1 index row1Bound bound
  have point2Canonical : ∀ index (bound : index < point2.val.length),
      GeneratedCanonicalQM31 (point2.val[index]'bound) := by
    intro index bound
    exact canonical_points_entry chain.outer.points pointsCanonical 2 index row2Bound bound
  have mPoint0Canonical := vector_point_canonical point0 prepared.mPoint0
    point0Exact point0Canonical
  have mPoint1Canonical := vector_point_canonical point1 prepared.mPoint1
    point1Exact point1Canonical
  have mPoint2Canonical := vector_point_canonical point2 prepared.mPoint2
    point2Exact point2Canonical
  have mPoint0Length := vector_point_length point0 prepared.mPoint0 point0Exact
  have mPoint1Length := vector_point_length point1 prepared.mPoint1 point1Exact
  have mPoint2Length := vector_point_length point2 prepared.mPoint2 point2Exact
  have tScale0Canonical :=
    V7CallerCurrentReleaseR30CircleArithmeticCanonical.AcceptedCircleStep.scale_canonical
      accumulator.step0
  have tScale1Canonical :=
    V7CallerCurrentReleaseR30CircleArithmeticCanonical.AcceptedCircleStep.scale_canonical
      accumulator.step1
  have tFactors0Canonical :=
    V7CallerCurrentReleaseR30CircleFactorsTerminalBridge.AcceptedCircleStep.tensor_factors_canonical
      accumulator.step0
  have tFactors1Canonical :=
    V7CallerCurrentReleaseR30CircleFactorsTerminalBridge.AcceptedCircleStep.tensor_factors_canonical
      accumulator.step1
  have tFactors0LengthRaw :=
    V7CallerCurrentReleaseR30CircleArithmeticCanonical.AcceptedCircleStep.factors_length
      accumulator.step0
  have tFactors0Length : accumulator.step0.factors.val.length = 10 := by
    change accumulator.step0.factors.val.length =
      (UScalar.cast .Usize prepared.circle.weightsAfterPrepared.log_len).val
      at tFactors0LengthRaw
    rw [prepared.logLenExact] at tFactors0LengthRaw
    simpa [cast_ten_u32_to_usize] using tFactors0LengthRaw
  have state1Log : accumulator.state1.2.2.2.2.log_len = 10#u32 := by
    calc
      accumulator.state1.2.2.2.2.log_len = accumulator.step0.weightsAfter.log_len :=
        congrArg (fun state => state.2.2.2.2.log_len) accumulator.step0.nextExact
      _ = prepared.circle.weightsAfterPrepared.log_len :=
        accumulator.step0.logLenExact
      _ = 10#u32 := prepared.logLenExact
  have tFactors1LengthRaw :=
    V7CallerCurrentReleaseR30CircleArithmeticCanonical.AcceptedCircleStep.factors_length
      accumulator.step1
  have tFactors1Length : accumulator.step1.factors.val.length = 10 := by
    change accumulator.step1.factors.val.length =
      (UScalar.cast .Usize accumulator.state1.2.2.2.2.log_len).val
      at tFactors1LengthRaw
    rw [state1Log] at tFactors1LengthRaw
    simpa [cast_ten_u32_to_usize] using tFactors1LengthRaw
  have inputLogLen : accumulator.origin.state.2.2.2.2.log_len = 10#u32 := by
    calc
      accumulator.origin.state.2.2.2.2.log_len = accumulator.state2.2.2.2.2.log_len := by
        rw [accumulator.originStateExact]
      _ = accumulator.step1.weightsAfter.log_len :=
        congrArg (fun state => state.2.2.2.2.log_len) accumulator.step1.nextExact
      _ = accumulator.state1.2.2.2.2.log_len := accumulator.step1.logLenExact
      _ = 10#u32 := state1Log
  obtain ⟨semantics⟩ := initial_fold_six_corresponds
    accumulator.origin.state.2.2.2.2 dispatch.initialFold.alpha
    dispatch.initialFold.weights trace prepared.mScale0 prepared.mScale1
    prepared.mScale2 prepared.mPoint0 prepared.mPoint1 prepared.mPoint2
    prepared.rowGroups prepared.groupMasks (alloc.vec.Vec.new field.QM31)
    accumulator.step0.scale accumulator.step1.scale accumulator.step0.factors
    accumulator.step1.factors inputLogLen accumulator.componentsExact
    dispatch.initialFold.alpha_canonical mScale0Canonical mScale1Canonical
    mScale2Canonical mPoint0Canonical mPoint1Canonical mPoint2Canonical
    mPoint0Length mPoint1Length mPoint2Length tScale0Canonical tScale1Canonical
    tFactors0Canonical tFactors1Canonical tFactors0Length tFactors1Length
  exact ⟨⟨inner, chain, prepared, accumulator, dispatch, trace, semantics⟩⟩

#print axioms reaches_r26_prechallenge_reaches_current_initial_fold_semantics

end AspisV7ProductionSnapshotObserverR30InitialFoldSemantics

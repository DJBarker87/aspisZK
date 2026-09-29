import V7CallerCurrentReleaseR26FirstFoldMergeSemantics
import V7CallerCurrentReleaseR26TailSixSemantics

/-!
# End-to-end semantics of the accepted optimized weight fold

A successful public `fold_tag73_relation_tail_arity4` call is inverted once.
The resulting first fold, multilinear merge, and fused six-component tail are
then connected to their maintained K1 semantics without exposing intermediate
states as assumptions of the public theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26AcceptedWeightFoldSemantics

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26TailWeightFoldTrace
open V7CallerCurrentReleaseR26WeightFoldLoopTrace
open V7CallerCurrentReleaseR26FirstFoldSevenSemantics
open V7CallerCurrentReleaseR26FirstFoldMergeSemantics
open V7CallerCurrentReleaseR26TailSixSemantics
open V7CallerCurrentReleaseR26GroupedRows
open V7CallerCurrentReleaseR26GroupedFold
open V7CallerCurrentReleaseR26GroupedRowsSemantics
open V7CallerCurrentReleaseR26GroupedLowSemantics
open V7CallerCurrentReleaseR26LineBatchFoldLoop
open V7CallerCurrentReleaseR26K1LineBatchFoldBridge

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31

structure AcceptedWeightFoldSemantics
    (input : sumcheck.WeightAccumulator)
    (alphas : Array RawQM31 3#usize)
    (output : sumcheck.WeightAccumulator)
    (mScale0 mScale1 mScale2 : RawQM31)
    (mPoint0 mPoint1 mPoint2 : alloc.vec.Vec RawQM31)
    (deferredAlpha : RawQM31)
    (groupValues : alloc.vec.Vec RawQM31)
    (tScale0 tScale1 : RawQM31)
    (tFactors0 tFactors1 : alloc.vec.Vec RawQM31)
    (lineScales : alloc.vec.Vec RawQM31)
    (lineXs : alloc.vec.Vec RawM31) : Type where
  trace : AcceptedTailWeightFoldTrace input alphas output
  firstTrace : FirstDeferredFoldTrace input trace.alpha0 trace.afterFirst
  first : FirstFoldSevenSemantics input trace.afterFirst trace.alpha0 firstTrace
    mScale0 mScale1 mScale2 mPoint0 mPoint1 mPoint2 deferredAlpha groupValues
    tScale0 tScale1 tFactors0 tFactors1 lineScales lineXs
  merge : FirstFoldMergeSemantics trace.afterFirst trace.afterMerge
    first.source.mScale0Out first.source.mScale1Out first.source.mScale2Out
    first.source.mPoint0Out first.source.mPoint1Out first.source.mPoint2Out
    (.Grouped64x16BinaryDeferred first.source.rowGroupsOut
      first.source.groupMasksOut first.source.firstAlphaOut
      first.source.groupValuesOut)
    (.Tensor first.source.tScale0Out first.source.tFactors0Out)
    (.Tensor first.source.tScale1Out first.source.tFactors1Out)
    (.LineM31Batch
      ((alloc.vec.Vec.deref_mut lineScales).2 first.source.lineScalesSliceOut)
      ((alloc.vec.Vec.deref_mut lineXs).2 first.source.lineXsSliceOut)
      first.source.lineDeferredOut)
  tail : TailSixSemantics trace merge.source.mergedScale
    first.source.mScale1Out first.source.mPoint0Out first.source.mPoint1Out
    first.source.rowGroupsOut first.source.groupMasksOut
    first.source.firstAlphaOut first.source.groupValuesOut
    first.source.tScale0Out first.source.tScale1Out
    first.source.tFactors0Out first.source.tFactors1Out
    ((alloc.vec.Vec.deref_mut lineScales).2 first.source.lineScalesSliceOut)
    ((alloc.vec.Vec.deref_mut lineXs).2 first.source.lineXsSliceOut)
    first.source.lineDeferredOut

theorem accepted_weight_fold_corresponds
    (input : sumcheck.WeightAccumulator)
    (alphas : Array RawQM31 3#usize)
    (output : sumcheck.WeightAccumulator)
    (mScale0 mScale1 mScale2 : RawQM31)
    (mPoint0 mPoint1 mPoint2 : alloc.vec.Vec RawQM31)
    (deferredAlpha : RawQM31)
    (groupValues : alloc.vec.Vec RawQM31)
    (tScale0 tScale1 : RawQM31)
    (tFactors0 tFactors1 : alloc.vec.Vec RawQM31)
    (lineScales : alloc.vec.Vec RawQM31)
    (lineXs : alloc.vec.Vec RawM31)
    (inputComponents : input.components.val =
      [.Multilinear mScale0 mPoint0,
       .Multilinear mScale1 mPoint1,
       .Multilinear mScale2 mPoint2,
       .Grouped64x16BinaryDeferred releasedRowGroups64 releasedMasks
         (some deferredAlpha) groupValues,
       .Tensor tScale0 tFactors0,
       .Tensor tScale1 tFactors1,
       .LineM31Batch lineScales lineXs 0#u8])
    (deferredAlphaCanonical : GeneratedCanonicalQM31 deferredAlpha)
    (alpha0Canonical : ∀ trace : AcceptedTailWeightFoldTrace input alphas output,
      GeneratedCanonicalQM31 trace.alpha0)
    (alpha1Canonical : ∀ trace : AcceptedTailWeightFoldTrace input alphas output,
      GeneratedCanonicalQM31 trace.alpha1)
    (alpha2Canonical : ∀ trace : AcceptedTailWeightFoldTrace input alphas output,
      GeneratedCanonicalQM31 trace.alpha2)
    (mScale0Canonical : GeneratedCanonicalQM31 mScale0)
    (mScale1Canonical : GeneratedCanonicalQM31 mScale1)
    (mScale2Canonical : GeneratedCanonicalQM31 mScale2)
    (mPoint0Canonical :
      V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
        mPoint0.val)
    (mPoint1Canonical :
      V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
        mPoint1.val)
    (mPoint2Canonical :
      V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
        mPoint2.val)
    (mPoint0Length : mPoint0.val.length = 8)
    (mPoint1Length : mPoint1.val.length = 8)
    (mPoint2Length : mPoint2.val.length = 8)
    (tScale0Canonical : GeneratedCanonicalQM31 tScale0)
    (tScale1Canonical : GeneratedCanonicalQM31 tScale1)
    (tFactors0Canonical :
      V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList tFactors0.val)
    (tFactors1Canonical :
      V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList tFactors1.val)
    (tFactors0Length : tFactors0.val.length = 8)
    (tFactors1Length : tFactors1.val.length = 8)
    (lineScalesLength : lineScales.val.length = 16)
    (lineXsLength : lineXs.val.length = 16)
    (lineScalesCanonical : CanonicalQM31Slice (alloc.vec.Vec.deref lineScales))
    (lineXsCanonical : CanonicalM31Slice (alloc.vec.Vec.deref lineXs))
    (run : sumcheck.WeightAccumulator.impl.fold_tag73_relation_tail_arity4
      input alphas = ok (true, output)) :
    Nonempty (AcceptedWeightFoldSemantics input alphas output mScale0 mScale1
      mScale2 mPoint0 mPoint1 mPoint2 deferredAlpha groupValues tScale0
      tScale1 tFactors0 tFactors1 lineScales lineXs) := by
  obtain ⟨trace⟩ := accepted_tail_weight_fold_exposes_trace input alphas
    output run
  obtain ⟨firstTrace⟩ := first_deferred_fold_exposes_exact_trace
    trace.firstFoldRun
  obtain ⟨first, _⟩ := first_fold_seven_corresponds input trace.afterFirst
    trace.alpha0 firstTrace mScale0 mScale1 mScale2 mPoint0 mPoint1 mPoint2
    deferredAlpha groupValues tScale0 tScale1 tFactors0 tFactors1 lineScales
    lineXs trace.inputLogLen inputComponents deferredAlphaCanonical
    (alpha0Canonical trace) mScale0Canonical mScale1Canonical mScale2Canonical
    mPoint0Canonical mPoint1Canonical mPoint2Canonical mPoint0Length
    mPoint1Length mPoint2Length tScale0Canonical tScale1Canonical
    tFactors0Canonical tFactors1Canonical tFactors0Length tFactors1Length
    lineScalesLength lineXsLength lineScalesCanonical lineXsCanonical
  obtain ⟨merge⟩ := first_fold_seven_then_merge_corresponds input
    trace.afterFirst trace.afterMerge trace.alpha0 firstTrace mScale0 mScale1
    mScale2 mPoint0 mPoint1 mPoint2 deferredAlpha groupValues tScale0 tScale1
    tFactors0 tFactors1 lineScales lineXs first trace.mergeRun
  have lowValuesExact : first.source.groupValuesOut =
      releasedSevenValues first.groupTrace.trace0.value
        first.groupTrace.trace1.value first.groupTrace.trace2.value
        first.groupTrace.trace3.value first.groupTrace.trace4.value
        first.groupTrace.trace5.value first.groupTrace.trace6.value := by
    calc
      first.source.groupValuesOut = releasedLowSevenValues
          first.groupTrace.trace0.value first.groupTrace.trace1.value
          first.groupTrace.trace2.value first.groupTrace.trace3.value
          first.groupTrace.trace4.value first.groupTrace.trace5.value
          first.groupTrace.trace6.value := first.groupValuesExact
      _ = releasedSevenValues first.groupTrace.trace0.value
          first.groupTrace.trace1.value first.groupTrace.trace2.value
          first.groupTrace.trace3.value first.groupTrace.trace4.value
          first.groupTrace.trace5.value first.groupTrace.trace6.value := by
            apply Subtype.ext
            rfl
  have lowValuesCanonical : CanonicalSeven first.groupTrace.trace0.value
      first.groupTrace.trace1.value first.groupTrace.trace2.value
      first.groupTrace.trace3.value first.groupTrace.trace4.value
      first.groupTrace.trace5.value first.groupTrace.trace6.value :=
    ⟨first.groupLowSemantics.canonical0,
     first.groupLowSemantics.canonical1,
     first.groupLowSemantics.canonical2,
     first.groupLowSemantics.canonical3,
     first.groupLowSemantics.canonical4,
     first.groupLowSemantics.canonical5,
     first.groupLowSemantics.canonical6⟩
  have lineScalesRoundtrip :
      (alloc.vec.Vec.deref_mut
        ((alloc.vec.Vec.deref_mut lineScales).2
          first.source.lineScalesSliceOut)).1 =
        first.source.lineScalesSliceOut := by
    apply Subtype.ext
    rfl
  have lineXsRoundtrip :
      (alloc.vec.Vec.deref_mut
        ((alloc.vec.Vec.deref_mut lineXs).2 first.source.lineXsSliceOut)).1 =
        first.source.lineXsSliceOut := by
    apply Subtype.ext
    rfl
  obtain ⟨tail⟩ := accepted_tail_six_components_correspond trace
    merge.source.mergedScale first.source.mScale1Out
    first.source.mPoint0Out first.source.mPoint1Out first.source.rowGroupsOut
    first.source.groupMasksOut first.source.firstAlphaOut
    first.source.groupValuesOut first.source.tScale0Out
    first.source.tScale1Out first.source.tFactors0Out
    first.source.tFactors1Out
    ((alloc.vec.Vec.deref_mut lineScales).2 first.source.lineScalesSliceOut)
    ((alloc.vec.Vec.deref_mut lineXs).2 first.source.lineXsSliceOut)
    first.source.lineDeferredOut first.groupTrace.trace0.value
    first.groupTrace.trace1.value first.groupTrace.trace2.value
    first.groupTrace.trace3.value first.groupTrace.trace4.value
    first.groupTrace.trace5.value first.groupTrace.trace6.value
    merge.source.componentsExact merge.mergedScaleCanonical
    first.mScale1Canonical first.mPoint0Canonical first.mPoint1Canonical
    first.mPoint0Length first.mPoint1Length first.groupRowsExact lowValuesExact
    lowValuesCanonical first.tScale0Canonical first.tScale1Canonical
    first.tFactors0Canonical first.tFactors1Canonical first.tFactors0Length
    first.tFactors1Length
    (by rw [lineScalesRoundtrip]; exact first.lineScalesLength)
    (by rw [lineXsRoundtrip]; exact first.lineXsLength)
    (by have h := first.lineDeferredExact; omega)
    (by rw [lineScalesRoundtrip]; exact first.lineScalesCanonical)
    (by rw [lineXsRoundtrip]; exact first.lineXsCanonical)
    (alpha1Canonical trace) (alpha2Canonical trace)
  exact ⟨{
    trace := trace
    firstTrace := firstTrace
    first := first
    merge := merge
    tail := tail }⟩

#print axioms accepted_weight_fold_corresponds

end V7CallerCurrentReleaseR26AcceptedWeightFoldSemantics

import V7CallerCurrentReleaseR26TailSixSource
import V7CallerCurrentReleaseR26TailGroupedTwoFoldSemantics

/-!
# Complete six-component semantics of the accepted fused tail

This module fixes the post-merge component order and applies the corresponding
source-to-K1 theorem to every output cell retained by the accepted traversal.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TailSixSemantics

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26TailWeightFoldTrace
open V7CallerCurrentReleaseR26TailSixSource
open V7CallerCurrentReleaseR26TailTwoFoldSemantics
open V7CallerCurrentReleaseR26TailGroupedTwoFoldSemantics
open V7CallerCurrentReleaseR26GroupedRows
open V7CallerCurrentReleaseR26GroupedRowsSemantics
open V7CallerCurrentReleaseR26LineBatchFoldLoop
open V7CallerCurrentReleaseR26K1LineBatchFoldBridge

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31
abbrev Component := sumcheck.WeightComponent

structure TailSixSemantics
    {input : sumcheck.WeightAccumulator}
    {alphas : Array RawQM31 3#usize}
    {output : sumcheck.WeightAccumulator}
    (tail : AcceptedTailWeightFoldTrace input alphas output)
    (mScale0 mScale1 : RawQM31)
    (mPoint0 mPoint1 : alloc.vec.Vec RawQM31)
    (rowGroups : alloc.vec.Vec Std.U8)
    (groupMasks : alloc.vec.Vec Std.U16)
    (firstAlpha : Option RawQM31)
    (groupValues : alloc.vec.Vec RawQM31)
    (tScale0 tScale1 : RawQM31)
    (tFactors0 tFactors1 : alloc.vec.Vec RawQM31)
    (lineScales : alloc.vec.Vec RawQM31)
    (lineXs : alloc.vec.Vec RawM31)
    (lineDeferred : Std.U8) : Type where
  source : TailSixSourceTrace tail
    (.Multilinear mScale0 mPoint0)
    (.Multilinear mScale1 mPoint1)
    (.Grouped64x16BinaryDeferred rowGroups groupMasks firstAlpha groupValues)
    (.Tensor tScale0 tFactors0)
    (.Tensor tScale1 tFactors1)
    (.LineM31Batch lineScales lineXs lineDeferred)
  multilinear0 : TailMultilinearSemantics tail mScale0 mPoint0 source.out0
  multilinear1 : TailMultilinearSemantics tail mScale1 mPoint1 source.out1
  grouped : TailGroupedSemantics tail rowGroups groupMasks firstAlpha
    groupValues source.out2
  tensor0 : TailTensorSemantics tail tScale0 tFactors0 source.out3
  tensor1 : TailTensorSemantics tail tScale1 tFactors1 source.out4
  line : TailLineBatchSemantics tail lineScales lineXs lineDeferred source.out5

theorem accepted_tail_six_components_correspond
    {input : sumcheck.WeightAccumulator}
    {alphas : Array RawQM31 3#usize}
    {output : sumcheck.WeightAccumulator}
    (tail : AcceptedTailWeightFoldTrace input alphas output)
    (mScale0 mScale1 : RawQM31)
    (mPoint0 mPoint1 : alloc.vec.Vec RawQM31)
    (rowGroups : alloc.vec.Vec Std.U8)
    (groupMasks : alloc.vec.Vec Std.U16)
    (firstAlpha : Option RawQM31)
    (groupValues : alloc.vec.Vec RawQM31)
    (tScale0 tScale1 : RawQM31)
    (tFactors0 tFactors1 : alloc.vec.Vec RawQM31)
    (lineScales : alloc.vec.Vec RawQM31)
    (lineXs : alloc.vec.Vec RawM31)
    (lineDeferred : Std.U8)
    (value0 value1 value2 value3 value4 value5 value6 : RawQM31)
    (componentsExact : tail.afterMerge.components.val =
      [.Multilinear mScale0 mPoint0,
       .Multilinear mScale1 mPoint1,
       .Grouped64x16BinaryDeferred rowGroups groupMasks firstAlpha groupValues,
       .Tensor tScale0 tFactors0,
       .Tensor tScale1 tFactors1,
       .LineM31Batch lineScales lineXs lineDeferred])
    (mScale0Canonical : GeneratedCanonicalQM31 mScale0)
    (mScale1Canonical : GeneratedCanonicalQM31 mScale1)
    (mPoint0Canonical :
      V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
        mPoint0.val)
    (mPoint1Canonical :
      V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
        mPoint1.val)
    (mPoint0Length : mPoint0.val.length = 6)
    (mPoint1Length : mPoint1.val.length = 6)
    (rowsExact : rowGroups = releasedRowGroups64)
    (valuesExact : groupValues =
      releasedSevenValues value0 value1 value2 value3 value4 value5 value6)
    (valuesCanonical : CanonicalSeven value0 value1 value2 value3 value4
      value5 value6)
    (tScale0Canonical : GeneratedCanonicalQM31 tScale0)
    (tScale1Canonical : GeneratedCanonicalQM31 tScale1)
    (tFactors0Canonical :
      V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList tFactors0.val)
    (tFactors1Canonical :
      V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList tFactors1.val)
    (tFactors0Length : tFactors0.val.length = 6)
    (tFactors1Length : tFactors1.val.length = 6)
    (lineScalesLength : (alloc.vec.Vec.deref_mut lineScales).1.val.length = 16)
    (lineXsLength : (alloc.vec.Vec.deref_mut lineXs).1.val.length = 16)
    (lineDeferredBound : lineDeferred.val ≤ 249)
    (lineScalesCanonical :
      CanonicalQM31Slice (alloc.vec.Vec.deref_mut lineScales).1)
    (lineXsCanonical : CanonicalM31Slice (alloc.vec.Vec.deref_mut lineXs).1)
    (alpha1Canonical : GeneratedCanonicalQM31 tail.alpha1)
    (alpha2Canonical : GeneratedCanonicalQM31 tail.alpha2) :
    Nonempty (TailSixSemantics tail mScale0 mScale1 mPoint0 mPoint1
      rowGroups groupMasks firstAlpha groupValues tScale0 tScale1 tFactors0
      tFactors1 lineScales lineXs lineDeferred) := by
  obtain ⟨source⟩ := accepted_tail_exposes_six_source_components tail
    (.Multilinear mScale0 mPoint0)
    (.Multilinear mScale1 mPoint1)
    (.Grouped64x16BinaryDeferred rowGroups groupMasks firstAlpha groupValues)
    (.Tensor tScale0 tFactors0)
    (.Tensor tScale1 tFactors1)
    (.LineM31Batch lineScales lineXs lineDeferred) componentsExact
  obtain ⟨multilinear0⟩ := tail_multilinear_step_corresponds tail mScale0
    mPoint0 source.out0 mScale0Canonical mPoint0Canonical mPoint0Length
    alpha1Canonical alpha2Canonical source.fold0
  obtain ⟨multilinear1⟩ := tail_multilinear_step_corresponds tail mScale1
    mPoint1 source.out1 mScale1Canonical mPoint1Canonical mPoint1Length
    alpha1Canonical alpha2Canonical source.fold1
  obtain ⟨grouped⟩ := tail_grouped_step_corresponds tail rowGroups
    groupMasks firstAlpha groupValues source.out2 value0 value1 value2 value3
    value4 value5 value6 rowsExact valuesExact valuesCanonical alpha1Canonical
    alpha2Canonical source.fold2
  obtain ⟨tensor0⟩ := tail_tensor_step_corresponds tail tScale0 tFactors0
    source.out3 tScale0Canonical tFactors0Canonical tFactors0Length
    alpha1Canonical alpha2Canonical source.fold3
  obtain ⟨tensor1⟩ := tail_tensor_step_corresponds tail tScale1 tFactors1
    source.out4 tScale1Canonical tFactors1Canonical tFactors1Length
    alpha1Canonical alpha2Canonical source.fold4
  obtain ⟨line⟩ := tail_line_batch_step_corresponds tail lineScales lineXs
    lineDeferred source.out5 lineScalesLength lineXsLength lineDeferredBound
    lineScalesCanonical lineXsCanonical alpha1Canonical alpha2Canonical
    source.fold5
  exact ⟨{
    source := source
    multilinear0 := multilinear0
    multilinear1 := multilinear1
    grouped := grouped
    tensor0 := tensor0
    tensor1 := tensor1
    line := line }⟩

#print axioms accepted_tail_six_components_correspond

end V7CallerCurrentReleaseR26TailSixSemantics

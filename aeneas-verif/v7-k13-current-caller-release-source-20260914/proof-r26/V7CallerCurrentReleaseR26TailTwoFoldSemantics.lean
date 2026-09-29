import V7CallerCurrentReleaseR26TailSixDispatch
import V7CallerCurrentReleaseR26K1StructuredWeightBridge
import V7CallerCurrentReleaseR26K1LineBatchFoldBridge

/-!
# K1 semantics of the fused tail's structured components

The generated fused step performs one arity-four fold at `alpha1` and one at
`alpha2`.  These theorems compose the existing source refinements into the
two-layer K1 meaning for multilinear and tensor components.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TailTwoFoldSemantics

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26TailWeightFoldTrace
open V7CallerCurrentReleaseR26TailSixDispatch
open V7CallerCurrentReleaseR26K1StructuredWeightBridge
open V7CallerCurrentReleaseR26LineBatchFoldLoop
open V7CallerCurrentReleaseR26LineBatchFold
open V7CallerCurrentReleaseR26K1LineBatchFoldBridge

abbrev RawQM31 := field.QM31
abbrev Component := sumcheck.WeightComponent

structure TailMultilinearSemantics
    {input : sumcheck.WeightAccumulator}
    {alphas : Array RawQM31 3#usize}
    {output : sumcheck.WeightAccumulator}
    (tail : AcceptedTailWeightFoldTrace input alphas output)
    (scale : RawQM31) (point : alloc.vec.Vec RawQM31)
    (componentOut : Component) : Type where
  source : TailMultilinearSourceTrace tail scale point componentOut
  finalScaleCanonical : GeneratedCanonicalQM31 source.scaleTwo
  finalPointCanonical :
    V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
      source.pointTwo.val
  finalPointLength : source.pointTwo.val.length = 2
  outputWeights :
    AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 4
        (exactRaw tail.alpha2)
        (AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 16
          (exactRaw tail.alpha1)
          (structuredComponentWeights .multilinear 3 scale point.val)) =
      structuredComponentWeights .multilinear 1 source.scaleTwo
        source.pointTwo.val

theorem tail_multilinear_step_corresponds
    {input : sumcheck.WeightAccumulator}
    {alphas : Array RawQM31 3#usize}
    {output : sumcheck.WeightAccumulator}
    (tail : AcceptedTailWeightFoldTrace input alphas output)
    (scale : RawQM31) (point : alloc.vec.Vec RawQM31)
    (componentOut : Component)
    (scaleCanonical : GeneratedCanonicalQM31 scale)
    (pointCanonical :
      V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
        point.val)
    (pointLength : point.val.length = 6)
    (alpha1Canonical : GeneratedCanonicalQM31 tail.alpha1)
    (alpha2Canonical : GeneratedCanonicalQM31 tail.alpha2)
    (run : V7CallerCurrentReleaseR26TailComponentTrace.foldTailComponent
      alphas (Array.make 2#usize [tail.alpha1Squared, tail.alpha2Squared])
      (Array.make 2#usize [tail.preparedAlpha1, tail.preparedAlpha2])
      (Array.make 2#usize
        [tail.preparedAlpha1Squared, tail.preparedAlpha2Squared])
      (Array.make 2#usize [tail.alpha1Cubed, tail.alpha2Cubed])
      (.Multilinear scale point) = ok (some componentOut)) :
    Nonempty (TailMultilinearSemantics tail scale point componentOut) := by
  obtain ⟨source⟩ := tail_multilinear_step_exposes_source tail scale point
    componentOut run
  have powers := tail.power_facts alpha1Canonical alpha2Canonical
  obtain ⟨scaleOneCanonical, pointOneCanonical, pointOneLength,
      firstWeights⟩ := fold_multilinear_arity4_transports_weights
    scale point tail.alpha1 tail.alpha1Squared tail.alpha1Cubed 2
    (by omega) (by omega) scaleCanonical pointCanonical alpha1Canonical
    powers.alpha1SquaredCanonical powers.alpha1CubedCanonical
    powers.alpha1SquaredExact powers.alpha1CubedExact source.scaleOne
    source.pointOne source.firstRun
  obtain ⟨scaleTwoCanonical, pointTwoCanonical, pointTwoLength,
      secondWeights⟩ := fold_multilinear_arity4_transports_weights
    source.scaleOne source.pointOne tail.alpha2 tail.alpha2Squared
    tail.alpha2Cubed 1 (by omega) (by omega) scaleOneCanonical
    pointOneCanonical alpha2Canonical powers.alpha2SquaredCanonical
    powers.alpha2CubedCanonical powers.alpha2SquaredExact
    powers.alpha2CubedExact source.scaleTwo source.pointTwo source.secondRun
  have firstWeights' :
      AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 16
          (exactRaw tail.alpha1)
          (structuredComponentWeights .multilinear 3 scale point.val) =
        structuredComponentWeights .multilinear 2 source.scaleOne
          source.pointOne.val := by
    simpa [radix4Size] using firstWeights
  have secondWeights' :
      AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 4
          (exactRaw tail.alpha2)
          (structuredComponentWeights .multilinear 2 source.scaleOne
            source.pointOne.val) =
        structuredComponentWeights .multilinear 1 source.scaleTwo
          source.pointTwo.val := by
    simpa [radix4Size] using secondWeights
  exact ⟨{
    source := source
    finalScaleCanonical := scaleTwoCanonical
    finalPointCanonical := pointTwoCanonical
    finalPointLength := pointTwoLength
    outputWeights := by rw [firstWeights', secondWeights'] }⟩

structure TailTensorSemantics
    {input : sumcheck.WeightAccumulator}
    {alphas : Array RawQM31 3#usize}
    {output : sumcheck.WeightAccumulator}
    (tail : AcceptedTailWeightFoldTrace input alphas output)
    (scale : RawQM31) (factors : alloc.vec.Vec RawQM31)
    (componentOut : Component) : Type where
  source : TailTensorSourceTrace tail scale factors componentOut
  finalScaleCanonical : GeneratedCanonicalQM31 source.scaleTwo
  finalFactorsCanonical :
    V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList
      source.factorsTwo.val
  finalFactorsLength : source.factorsTwo.val.length = 2
  outputWeights :
    AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 4
        (exactRaw tail.alpha2)
        (AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 16
          (exactRaw tail.alpha1)
          (structuredComponentWeights .tensor 3 scale factors.val)) =
      structuredComponentWeights .tensor 1 source.scaleTwo
        source.factorsTwo.val

theorem tail_tensor_step_corresponds
    {input : sumcheck.WeightAccumulator}
    {alphas : Array RawQM31 3#usize}
    {output : sumcheck.WeightAccumulator}
    (tail : AcceptedTailWeightFoldTrace input alphas output)
    (scale : RawQM31) (factors : alloc.vec.Vec RawQM31)
    (componentOut : Component)
    (scaleCanonical : GeneratedCanonicalQM31 scale)
    (factorsCanonical :
      V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList factors.val)
    (factorsLength : factors.val.length = 6)
    (alpha1Canonical : GeneratedCanonicalQM31 tail.alpha1)
    (alpha2Canonical : GeneratedCanonicalQM31 tail.alpha2)
    (run : V7CallerCurrentReleaseR26TailComponentTrace.foldTailComponent
      alphas (Array.make 2#usize [tail.alpha1Squared, tail.alpha2Squared])
      (Array.make 2#usize [tail.preparedAlpha1, tail.preparedAlpha2])
      (Array.make 2#usize
        [tail.preparedAlpha1Squared, tail.preparedAlpha2Squared])
      (Array.make 2#usize [tail.alpha1Cubed, tail.alpha2Cubed])
      (.Tensor scale factors) = ok (some componentOut)) :
    Nonempty (TailTensorSemantics tail scale factors componentOut) := by
  obtain ⟨source⟩ := tail_tensor_step_exposes_source tail scale factors
    componentOut run
  have powers := tail.power_facts alpha1Canonical alpha2Canonical
  obtain ⟨scaleOneCanonical, factorsOneCanonical, factorsOneLength,
      firstWeights⟩ := fold_tensor_arity4_transports_weights
    scale factors tail.alpha1 tail.alpha1Squared tail.alpha1Cubed
    tail.preparedAlpha1 tail.preparedAlpha1Squared 2 (by omega) (by omega)
    scaleCanonical factorsCanonical alpha1Canonical
    powers.alpha1SquaredCanonical powers.alpha1CubedCanonical
    powers.preparedAlpha1Represents powers.preparedAlpha1SquaredRepresents
    powers.alpha1SquaredExact powers.alpha1CubedExact source.scaleOne
    source.factorsOne source.firstRun
  obtain ⟨scaleTwoCanonical, factorsTwoCanonical, factorsTwoLength,
      secondWeights⟩ := fold_tensor_arity4_transports_weights
    source.scaleOne source.factorsOne tail.alpha2 tail.alpha2Squared
    tail.alpha2Cubed tail.preparedAlpha2 tail.preparedAlpha2Squared 1
    (by omega) (by omega) scaleOneCanonical factorsOneCanonical
    alpha2Canonical powers.alpha2SquaredCanonical
    powers.alpha2CubedCanonical powers.preparedAlpha2Represents
    powers.preparedAlpha2SquaredRepresents powers.alpha2SquaredExact
    powers.alpha2CubedExact source.scaleTwo source.factorsTwo source.secondRun
  have firstWeights' :
      AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 16
          (exactRaw tail.alpha1)
          (structuredComponentWeights .tensor 3 scale factors.val) =
        structuredComponentWeights .tensor 2 source.scaleOne
          source.factorsOne.val := by
    simpa [radix4Size] using firstWeights
  have secondWeights' :
      AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 4
          (exactRaw tail.alpha2)
          (structuredComponentWeights .tensor 2 source.scaleOne
            source.factorsOne.val) =
        structuredComponentWeights .tensor 1 source.scaleTwo
          source.factorsTwo.val := by
    simpa [radix4Size] using secondWeights
  exact ⟨{
    source := source
    finalScaleCanonical := scaleTwoCanonical
    finalFactorsCanonical := factorsTwoCanonical
    finalFactorsLength := factorsTwoLength
    outputWeights := by rw [firstWeights', secondWeights'] }⟩

structure TailLineBatchSemantics
    {input : sumcheck.WeightAccumulator}
    {alphas : Array RawQM31 3#usize}
    {output : sumcheck.WeightAccumulator}
    (tail : AcceptedTailWeightFoldTrace input alphas output)
    (scales : alloc.vec.Vec RawQM31) (xs : alloc.vec.Vec field.M31)
    (deferred : Std.U8) (componentOut : Component) : Type where
  source : TailLineBatchSourceTrace tail scales xs deferred componentOut
  finalScalesCanonical : CanonicalQM31Slice source.scalesTwo
  finalXsCanonical : CanonicalM31Slice source.xsTwo
  finalScalesLength : source.scalesTwo.val.length = 16
  finalXsLength : source.xsTwo.val.length = 16
  finalDeferredExact : source.deferredTwo.val = deferred.val + 4
  outputWeights :
    AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 4
        (exactRaw tail.alpha2)
        (AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 16
          (exactRaw tail.alpha1)
          (lineBatchComponentWeights 3 (alloc.vec.Vec.deref_mut scales).1
            (alloc.vec.Vec.deref_mut xs).1 deferred.val)) =
      lineBatchComponentWeights 1 source.scalesTwo source.xsTwo
        source.deferredTwo.val

theorem tail_line_batch_step_corresponds
    {input : sumcheck.WeightAccumulator}
    {alphas : Array RawQM31 3#usize}
    {output : sumcheck.WeightAccumulator}
    (tail : AcceptedTailWeightFoldTrace input alphas output)
    (scales : alloc.vec.Vec RawQM31) (xs : alloc.vec.Vec field.M31)
    (deferred : Std.U8) (componentOut : Component)
    (scalesLength : (alloc.vec.Vec.deref_mut scales).1.val.length = 16)
    (xsLength : (alloc.vec.Vec.deref_mut xs).1.val.length = 16)
    (deferredBound : deferred.val ≤ 249)
    (scalesCanonical :
      CanonicalQM31Slice (alloc.vec.Vec.deref_mut scales).1)
    (xsCanonical : CanonicalM31Slice (alloc.vec.Vec.deref_mut xs).1)
    (alpha1Canonical : GeneratedCanonicalQM31 tail.alpha1)
    (alpha2Canonical : GeneratedCanonicalQM31 tail.alpha2)
    (run : V7CallerCurrentReleaseR26TailComponentTrace.foldTailComponent
      alphas (Array.make 2#usize [tail.alpha1Squared, tail.alpha2Squared])
      (Array.make 2#usize [tail.preparedAlpha1, tail.preparedAlpha2])
      (Array.make 2#usize
        [tail.preparedAlpha1Squared, tail.preparedAlpha2Squared])
      (Array.make 2#usize [tail.alpha1Cubed, tail.alpha2Cubed])
      (.LineM31Batch scales xs deferred) = ok (some componentOut)) :
    Nonempty (TailLineBatchSemantics tail scales xs deferred
      componentOut) := by
  obtain ⟨source⟩ := tail_line_batch_step_exposes_source tail scales xs
    deferred componentOut run
  have powers := tail.power_facts alpha1Canonical alpha2Canonical
  obtain ⟨firstPrefix, deferredOneExact⟩ :=
    fold_line_m31_batch_arity4_exact
      (alloc.vec.Vec.deref_mut scales).1
      (alloc.vec.Vec.deref_mut xs).1 deferred tail.alpha1
      tail.alpha1Squared tail.alpha1Cubed source.scalesOne source.xsOne
      source.deferredOne scalesLength (by omega) (by omega)
      scalesCanonical xsCanonical alpha1Canonical
      powers.alpha1SquaredCanonical powers.alpha1CubedCanonical
      powers.alpha1SquaredExact powers.alpha1CubedExact source.firstRun
  have scalesOneRoundtrip :
      (alloc.vec.Vec.deref_mut
        ((alloc.vec.Vec.deref_mut scales).2 source.scalesOne)).1 =
        source.scalesOne := by
    apply Subtype.ext
    rfl
  have xsOneRoundtrip :
      (alloc.vec.Vec.deref_mut
        ((alloc.vec.Vec.deref_mut xs).2 source.xsOne)).1 = source.xsOne := by
    apply Subtype.ext
    rfl
  have secondScalesLength :
      (alloc.vec.Vec.deref_mut
        ((alloc.vec.Vec.deref_mut scales).2 source.scalesOne)).1.val.length =
          16 := by
    rw [scalesOneRoundtrip, firstPrefix.stateScalesLength]
    exact scalesLength
  have secondXsLength :
      (alloc.vec.Vec.deref_mut
        ((alloc.vec.Vec.deref_mut xs).2 source.xsOne)).1.val.length = 16 := by
    rw [xsOneRoundtrip, firstPrefix.stateXsLength]
    exact xsLength
  have secondScalesCanonical : CanonicalQM31Slice
      (alloc.vec.Vec.deref_mut
        ((alloc.vec.Vec.deref_mut scales).2 source.scalesOne)).1 := by
    simpa [scalesOneRoundtrip] using firstPrefix.currentScalesCanonical
  have secondXsCanonical : CanonicalM31Slice
      (alloc.vec.Vec.deref_mut
        ((alloc.vec.Vec.deref_mut xs).2 source.xsOne)).1 := by
    simpa [xsOneRoundtrip] using firstPrefix.currentXsCanonical
  obtain ⟨secondPrefix, deferredTwoStep⟩ :=
    fold_line_m31_batch_arity4_exact
      (alloc.vec.Vec.deref_mut
        ((alloc.vec.Vec.deref_mut scales).2 source.scalesOne)).1
      (alloc.vec.Vec.deref_mut
        ((alloc.vec.Vec.deref_mut xs).2 source.xsOne)).1
      source.deferredOne tail.alpha2 tail.alpha2Squared tail.alpha2Cubed
      source.scalesTwo source.xsTwo source.deferredTwo secondScalesLength
      (by omega) (by rw [deferredOneExact]; omega) secondScalesCanonical
      secondXsCanonical alpha2Canonical powers.alpha2SquaredCanonical
      powers.alpha2CubedCanonical powers.alpha2SquaredExact
      powers.alpha2CubedExact source.secondRun
  have firstProcessed := fold_line_m31_batch_arity4_processed
    (alloc.vec.Vec.deref_mut scales).1 (alloc.vec.Vec.deref_mut xs).1
    deferred tail.alpha1 tail.alpha1Squared tail.alpha1Cubed source.scalesOne
    source.xsOne source.deferredOne scalesLength (by omega) scalesCanonical
    xsCanonical alpha1Canonical powers.alpha1SquaredCanonical
    powers.alpha1CubedCanonical powers.alpha1SquaredExact
    powers.alpha1CubedExact source.firstRun
  have firstWeights := lineBatchFoldCompleted16_transports_weights 2
    (alloc.vec.Vec.deref_mut scales).1 (alloc.vec.Vec.deref_mut xs).1
    deferred tail.alpha1 source.scalesOne source.xsOne source.deferredOne
    firstProcessed deferredOneExact
  have secondProcessed := fold_line_m31_batch_arity4_processed
    (alloc.vec.Vec.deref_mut
      ((alloc.vec.Vec.deref_mut scales).2 source.scalesOne)).1
    (alloc.vec.Vec.deref_mut
      ((alloc.vec.Vec.deref_mut xs).2 source.xsOne)).1
    source.deferredOne tail.alpha2 tail.alpha2Squared tail.alpha2Cubed
    source.scalesTwo source.xsTwo source.deferredTwo secondScalesLength
    (by omega) secondScalesCanonical secondXsCanonical alpha2Canonical
    powers.alpha2SquaredCanonical powers.alpha2CubedCanonical
    powers.alpha2SquaredExact powers.alpha2CubedExact source.secondRun
  have secondWeights := lineBatchFoldCompleted16_transports_weights 1
    (alloc.vec.Vec.deref_mut
      ((alloc.vec.Vec.deref_mut scales).2 source.scalesOne)).1
    (alloc.vec.Vec.deref_mut
      ((alloc.vec.Vec.deref_mut xs).2 source.xsOne)).1
    source.deferredOne tail.alpha2 source.scalesTwo source.xsTwo
    source.deferredTwo secondProcessed deferredTwoStep
  have firstWeights' :
      AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 16
          (exactRaw tail.alpha1)
          (lineBatchComponentWeights 3 (alloc.vec.Vec.deref_mut scales).1
            (alloc.vec.Vec.deref_mut xs).1 deferred.val) =
        lineBatchComponentWeights 2 source.scalesOne source.xsOne
          source.deferredOne.val := by
    simpa [radix4Size] using firstWeights
  have secondWeights' :
      AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 4
          (exactRaw tail.alpha2)
          (lineBatchComponentWeights 2 source.scalesOne source.xsOne
            source.deferredOne.val) =
        lineBatchComponentWeights 1 source.scalesTwo source.xsTwo
          source.deferredTwo.val := by
    simpa [radix4Size, scalesOneRoundtrip, xsOneRoundtrip] using secondWeights
  exact ⟨{
    source := source
    finalScalesCanonical := secondPrefix.currentScalesCanonical
    finalXsCanonical := secondPrefix.currentXsCanonical
    finalScalesLength := by
      rw [secondPrefix.stateScalesLength]
      exact secondScalesLength
    finalXsLength := by
      rw [secondPrefix.stateXsLength]
      exact secondXsLength
    finalDeferredExact := by rw [deferredTwoStep, deferredOneExact]
    outputWeights := by rw [firstWeights', secondWeights'] }⟩

#print axioms tail_multilinear_step_corresponds
#print axioms tail_tensor_step_corresponds
#print axioms tail_line_batch_step_corresponds

end V7CallerCurrentReleaseR26TailTwoFoldSemantics

import V7CallerCurrentReleaseR26AcceptedWeightFoldSemantics

/-!
# Complete K1 weight vector of the accepted optimized fold

The component refinements are composed pointwise here.  The resulting theorem
identifies the six-component production accumulator at log length two with
three maintained K1 dual radix-four folds of its seven-component input.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26AcceptedWeightVectorSemantics

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26AcceptedWeightFoldSemantics
open V7CallerCurrentReleaseR26K1StructuredWeightBridge
open V7CallerCurrentReleaseR26K1LineBatchFoldBridge
open V7CallerCurrentReleaseR26GroupedInitialSemantics
open V7CallerCurrentReleaseR26GroupedRows
open V7CallerCurrentReleaseR26GroupedRowsSemantics
open V7CallerCurrentReleaseR26TailWeightFoldTrace
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriRelationCandidateBridge

abbrev RawQM31 := field.QM31
abbrev ModelQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

def sumSeven {n : Nat}
    (a b c d e f g : Fin n → ModelQM31) : Fin n → ModelQM31 :=
  fun index => a index + b index + c index + d index + e index + f index +
    g index

def sumSix {n : Nat}
    (a b c d e f : Fin n → ModelQM31) : Fin n → ModelQM31 :=
  fun index => a index + b index + c index + d index + e index + f index

private theorem dual_sumSeven {n : Nat} (alpha : ModelQM31)
    (a b c d e f g : Fin (4 * n) → ModelQM31) :
    dualWeightFoldLayer n alpha (sumSeven a b c d e f g) =
      sumSeven (dualWeightFoldLayer n alpha a)
        (dualWeightFoldLayer n alpha b) (dualWeightFoldLayer n alpha c)
        (dualWeightFoldLayer n alpha d) (dualWeightFoldLayer n alpha e)
        (dualWeightFoldLayer n alpha f) (dualWeightFoldLayer n alpha g) := by
  funext fibre
  unfold dualWeightFoldLayer dualWeightFoldValue sumSeven
  ring

private theorem dual_sumSix {n : Nat} (alpha : ModelQM31)
    (a b c d e f : Fin (4 * n) → ModelQM31) :
    dualWeightFoldLayer n alpha (sumSix a b c d e f) =
      sumSix (dualWeightFoldLayer n alpha a)
        (dualWeightFoldLayer n alpha b) (dualWeightFoldLayer n alpha c)
        (dualWeightFoldLayer n alpha d) (dualWeightFoldLayer n alpha e)
        (dualWeightFoldLayer n alpha f) := by
  funext fibre
  unfold dualWeightFoldLayer dualWeightFoldValue sumSix
  ring

def inputWeightVector
    (mScale0 mScale1 mScale2 : RawQM31)
    (mPoint0 mPoint1 mPoint2 : alloc.vec.Vec RawQM31)
    (deferredAlpha : RawQM31)
    (tScale0 tScale1 : RawQM31)
    (tFactors0 tFactors1 : alloc.vec.Vec RawQM31)
    (lineScales : alloc.vec.Vec RawQM31)
    (lineXs : alloc.vec.Vec field.M31) : Fin 256 → ModelQM31 :=
  sumSeven
    (structuredComponentWeights .multilinear 4 mScale0 mPoint0.val)
    (structuredComponentWeights .multilinear 4 mScale1 mPoint1.val)
    (structuredComponentWeights .multilinear 4 mScale2 mPoint2.val)
    (dualWeightFoldLayer 256 (exactRaw deferredAlpha)
      releasedInactiveInitialWeight)
    (structuredComponentWeights .tensor 4 tScale0 tFactors0.val)
    (structuredComponentWeights .tensor 4 tScale1 tFactors1.val)
    (lineBatchComponentWeights 4 (alloc.vec.Vec.deref lineScales)
      (alloc.vec.Vec.deref lineXs) 0)

def outputWeightVector
    {input : sumcheck.WeightAccumulator}
    {alphas : Array RawQM31 3#usize}
    {output : sumcheck.WeightAccumulator}
    {mScale0 mScale1 mScale2 : RawQM31}
    {mPoint0 mPoint1 mPoint2 : alloc.vec.Vec RawQM31}
    {deferredAlpha : RawQM31} {groupValues : alloc.vec.Vec RawQM31}
    {tScale0 tScale1 : RawQM31}
    {tFactors0 tFactors1 : alloc.vec.Vec RawQM31}
    {lineScales : alloc.vec.Vec RawQM31}
    {lineXs : alloc.vec.Vec field.M31}
    (semantics : AcceptedWeightFoldSemantics input alphas output mScale0
      mScale1 mScale2 mPoint0 mPoint1 mPoint2 deferredAlpha groupValues
      tScale0 tScale1 tFactors0 tFactors1 lineScales lineXs) :
    Fin 4 → ModelQM31 :=
  sumSix
    (structuredComponentWeights .multilinear 1
      semantics.tail.multilinear0.source.scaleTwo
      semantics.tail.multilinear0.source.pointTwo.val)
    (structuredComponentWeights .multilinear 1
      semantics.tail.multilinear1.source.scaleTwo
      semantics.tail.multilinear1.source.pointTwo.val)
    (representedGroupedWeights
      semantics.tail.grouped.source.foldedGroups
      semantics.tail.grouped.source.foldedValues)
    (structuredComponentWeights .tensor 1
      semantics.tail.tensor0.source.scaleTwo
      semantics.tail.tensor0.source.factorsTwo.val)
    (structuredComponentWeights .tensor 1
      semantics.tail.tensor1.source.scaleTwo
      semantics.tail.tensor1.source.factorsTwo.val)
    (lineBatchComponentWeights 1 semantics.tail.line.source.scalesTwo
      semantics.tail.line.source.xsTwo
      semantics.tail.line.source.deferredTwo.val)

structure AcceptedWeightVectorSemantics
    {input : sumcheck.WeightAccumulator}
    {alphas : Array RawQM31 3#usize}
    {output : sumcheck.WeightAccumulator}
    {mScale0 mScale1 mScale2 : RawQM31}
    {mPoint0 mPoint1 mPoint2 : alloc.vec.Vec RawQM31}
    {deferredAlpha : RawQM31} {groupValues : alloc.vec.Vec RawQM31}
    {tScale0 tScale1 : RawQM31}
    {tFactors0 tFactors1 : alloc.vec.Vec RawQM31}
    {lineScales : alloc.vec.Vec RawQM31}
    {lineXs : alloc.vec.Vec field.M31}
    (semantics : AcceptedWeightFoldSemantics input alphas output mScale0
      mScale1 mScale2 mPoint0 mPoint1 mPoint2 deferredAlpha groupValues
      tScale0 tScale1 tFactors0 tFactors1 lineScales lineXs) : Prop where
  outputLogExact : output.log_len = 2#u32
  outputComponentsExact : output.components.val =
    [semantics.tail.source.out0, semantics.tail.source.out1,
     semantics.tail.source.out2, semantics.tail.source.out3,
     semantics.tail.source.out4, semantics.tail.source.out5]
  finalWeightsExact :
    dualWeightFoldLayer 4 (exactRaw semantics.trace.alpha2)
        (dualWeightFoldLayer 16 (exactRaw semantics.trace.alpha1)
          (dualWeightFoldLayer 64 (exactRaw semantics.trace.alpha0)
            (inputWeightVector mScale0 mScale1 mScale2 mPoint0 mPoint1
              mPoint2 deferredAlpha tScale0 tScale1 tFactors0 tFactors1
              lineScales lineXs))) =
      outputWeightVector semantics

theorem accepted_weight_vector_corresponds
    {input : sumcheck.WeightAccumulator}
    {alphas : Array RawQM31 3#usize}
    {output : sumcheck.WeightAccumulator}
    {mScale0 mScale1 mScale2 : RawQM31}
    {mPoint0 mPoint1 mPoint2 : alloc.vec.Vec RawQM31}
    {deferredAlpha : RawQM31} {groupValues : alloc.vec.Vec RawQM31}
    {tScale0 tScale1 : RawQM31}
    {tFactors0 tFactors1 : alloc.vec.Vec RawQM31}
    {lineScales : alloc.vec.Vec RawQM31}
    {lineXs : alloc.vec.Vec field.M31}
    (semantics : AcceptedWeightFoldSemantics input alphas output mScale0
      mScale1 mScale2 mPoint0 mPoint1 mPoint2 deferredAlpha groupValues
      tScale0 tScale1 tFactors0 tFactors1 lineScales lineXs) :
    AcceptedWeightVectorSemantics semantics := by
  have firstFold :
      dualWeightFoldLayer 64 (exactRaw semantics.trace.alpha0)
          (inputWeightVector mScale0 mScale1 mScale2 mPoint0 mPoint1 mPoint2
            deferredAlpha tScale0 tScale1 tFactors0 tFactors1 lineScales
            lineXs) =
        sumSeven
          (structuredComponentWeights .multilinear 3
            semantics.first.source.mScale0Out
            semantics.first.source.mPoint0Out.val)
          (structuredComponentWeights .multilinear 3
            semantics.first.source.mScale1Out
            semantics.first.source.mPoint1Out.val)
          (structuredComponentWeights .multilinear 3
            semantics.first.source.mScale2Out
            semantics.first.source.mPoint2Out.val)
          (representedReleasedGroupedWeights releasedRowGroups64
            semantics.first.source.groupValuesOut)
          (structuredComponentWeights .tensor 3
            semantics.first.source.tScale0Out
            semantics.first.source.tFactors0Out.val)
          (structuredComponentWeights .tensor 3
            semantics.first.source.tScale1Out
            semantics.first.source.tFactors1Out.val)
          (lineBatchComponentWeights 3 semantics.first.source.lineScalesSliceOut
            semantics.first.source.lineXsSliceOut
            semantics.first.source.lineDeferredOut.val) := by
    unfold inputWeightVector
    rw [dual_sumSeven]
    rw [semantics.first.multilinear0Weights,
      semantics.first.multilinear1Weights,
      semantics.first.multilinear2Weights]
    rw [← semantics.first.groupedWeights]
    rw [semantics.first.tensor0Weights, semantics.first.tensor1Weights,
      semantics.first.lineBatchWeights]
    rfl
  have merged :
      sumSeven
          (structuredComponentWeights .multilinear 3
            semantics.first.source.mScale0Out
            semantics.first.source.mPoint0Out.val)
          (structuredComponentWeights .multilinear 3
            semantics.first.source.mScale1Out
            semantics.first.source.mPoint1Out.val)
          (structuredComponentWeights .multilinear 3
            semantics.first.source.mScale2Out
            semantics.first.source.mPoint2Out.val)
          (representedReleasedGroupedWeights releasedRowGroups64
            semantics.first.source.groupValuesOut)
          (structuredComponentWeights .tensor 3
            semantics.first.source.tScale0Out
            semantics.first.source.tFactors0Out.val)
          (structuredComponentWeights .tensor 3
            semantics.first.source.tScale1Out
            semantics.first.source.tFactors1Out.val)
          (lineBatchComponentWeights 3 semantics.first.source.lineScalesSliceOut
            semantics.first.source.lineXsSliceOut
            semantics.first.source.lineDeferredOut.val) =
        sumSix
          (structuredComponentWeights .multilinear 3
            semantics.merge.source.mergedScale
            semantics.first.source.mPoint0Out.val)
          (structuredComponentWeights .multilinear 3
            semantics.first.source.mScale1Out
            semantics.first.source.mPoint1Out.val)
          (representedGroupedWeights semantics.first.source.rowGroupsOut
            semantics.first.source.groupValuesOut)
          (structuredComponentWeights .tensor 3
            semantics.first.source.tScale0Out
            semantics.first.source.tFactors0Out.val)
          (structuredComponentWeights .tensor 3
            semantics.first.source.tScale1Out
            semantics.first.source.tFactors1Out.val)
          (lineBatchComponentWeights 3 semantics.first.source.lineScalesSliceOut
            semantics.first.source.lineXsSliceOut
            semantics.first.source.lineDeferredOut.val) := by
    funext index
    have mergeAt := congrFun semantics.merge.mergedWeights index
    have groupedAt :
        representedReleasedGroupedWeights releasedRowGroups64
            semantics.first.source.groupValuesOut index =
          representedGroupedWeights semantics.first.source.rowGroupsOut
            semantics.first.source.groupValuesOut index := by
      rw [semantics.first.groupRowsExact]
      rfl
    unfold sumSeven sumSix
    rw [mergeAt, groupedAt]
    ring
  have tailFold :
      dualWeightFoldLayer 4 (exactRaw semantics.trace.alpha2)
          (dualWeightFoldLayer 16 (exactRaw semantics.trace.alpha1)
            (sumSix
              (structuredComponentWeights .multilinear 3
                semantics.merge.source.mergedScale
                semantics.first.source.mPoint0Out.val)
              (structuredComponentWeights .multilinear 3
                semantics.first.source.mScale1Out
                semantics.first.source.mPoint1Out.val)
              (representedGroupedWeights semantics.first.source.rowGroupsOut
                semantics.first.source.groupValuesOut)
              (structuredComponentWeights .tensor 3
                semantics.first.source.tScale0Out
                semantics.first.source.tFactors0Out.val)
              (structuredComponentWeights .tensor 3
                semantics.first.source.tScale1Out
                semantics.first.source.tFactors1Out.val)
              (lineBatchComponentWeights 3
                semantics.first.source.lineScalesSliceOut
                semantics.first.source.lineXsSliceOut
                semantics.first.source.lineDeferredOut.val))) =
        outputWeightVector semantics := by
    have lineScalesRoundtrip :
        (alloc.vec.Vec.deref_mut
          ((alloc.vec.Vec.deref_mut lineScales).2
            semantics.first.source.lineScalesSliceOut)).1 =
          semantics.first.source.lineScalesSliceOut := by
      apply Subtype.ext
      rfl
    have lineXsRoundtrip :
        (alloc.vec.Vec.deref_mut
          ((alloc.vec.Vec.deref_mut lineXs).2
            semantics.first.source.lineXsSliceOut)).1 =
          semantics.first.source.lineXsSliceOut := by
      apply Subtype.ext
      rfl
    have lineWeights := semantics.tail.line.outputWeights
    rw [lineScalesRoundtrip, lineXsRoundtrip] at lineWeights
    rw [dual_sumSix, dual_sumSix]
    unfold outputWeightVector
    rw [semantics.tail.multilinear0.outputWeights,
      semantics.tail.multilinear1.outputWeights,
      ← semantics.tail.grouped.outputWeights,
      semantics.tail.tensor0.outputWeights,
      semantics.tail.tensor1.outputWeights,
      lineWeights]
  have outputLog := congrArg sumcheck.WeightAccumulator.log_len
    semantics.trace.outputExact
  have outputComponents := congrArg
    (fun weights : sumcheck.WeightAccumulator => weights.components.val)
    semantics.trace.outputExact
  refine ⟨outputLog.trans semantics.tail.source.finalLogExact, ?_, ?_⟩
  · exact outputComponents.trans semantics.tail.source.finalComponentsExact
  · rw [firstFold, merged]
    exact tailFold

#print axioms accepted_weight_vector_corresponds

end V7CallerCurrentReleaseR26AcceptedWeightVectorSemantics

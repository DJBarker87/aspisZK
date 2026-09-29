import V7CallerCurrentReleaseR26FirstFoldSevenSource
import V7CallerCurrentReleaseR26GroupedDeferredLog8
import V7CallerCurrentReleaseR26FirstFoldLineSemantics

/-!
# K1 semantics of the current seven-component first fold

Each exact source cell exposed by the traversal is transported through its
component-specific refinement theorem.  The result is the complete
log-eight-to-log-six semantic image used by the later merge and fused tail.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26FirstFoldSevenSemantics

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26WeightFoldLoopTrace
open V7CallerCurrentReleaseR26FirstFoldSevenSource
open V7CallerCurrentReleaseR26GroupedFold
open V7CallerCurrentReleaseR26GroupedRows
open V7CallerCurrentReleaseR26GroupedLowSemantics
open V7CallerCurrentReleaseR26GroupedInitialSemantics
open V7CallerCurrentReleaseR26GroupedDeferredLog8
open V7CallerCurrentReleaseR26K1StructuredWeightBridge
open V7CallerCurrentReleaseR26K1LineBatchFoldBridge
open V7CallerCurrentReleaseR26LineBatchFoldLoop
open V7CallerCurrentReleaseR26FirstFoldLineSemantics

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

private structure MultilinearFacts
    (alpha : RawQM31)
    (scale0 scale1 scale2 : RawQM31)
    (point0 point1 point2 : alloc.vec.Vec RawQM31)
    (scale0Out scale1Out scale2Out : RawQM31)
    (point0Out point1Out point2Out : alloc.vec.Vec RawQM31) : Prop where
  scale0Canonical : GeneratedCanonicalQM31 scale0Out
  scale1Canonical : GeneratedCanonicalQM31 scale1Out
  scale2Canonical : GeneratedCanonicalQM31 scale2Out
  point0Canonical :
    V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList point0Out.val
  point1Canonical :
    V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList point1Out.val
  point2Canonical :
    V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList point2Out.val
  point0Length : point0Out.val.length = 6
  point1Length : point1Out.val.length = 6
  point2Length : point2Out.val.length = 6
  weights0 :
    AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 64
        (exactRaw alpha)
        (structuredComponentWeights .multilinear 4 scale0 point0.val) =
      structuredComponentWeights .multilinear 3 scale0Out point0Out.val
  weights1 :
    AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 64
        (exactRaw alpha)
        (structuredComponentWeights .multilinear 4 scale1 point1.val) =
      structuredComponentWeights .multilinear 3 scale1Out point1Out.val
  weights2 :
    AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 64
        (exactRaw alpha)
        (structuredComponentWeights .multilinear 4 scale2 point2.val) =
      structuredComponentWeights .multilinear 3 scale2Out point2Out.val

private theorem multilinear_facts
    (alpha alpha2 alpha3 : RawQM31)
    (scale0 scale1 scale2 : RawQM31)
    (point0 point1 point2 : alloc.vec.Vec RawQM31)
    (scale0Out scale1Out scale2Out : RawQM31)
    (point0Out point1Out point2Out : alloc.vec.Vec RawQM31)
    (hscale0 : GeneratedCanonicalQM31 scale0)
    (hscale1 : GeneratedCanonicalQM31 scale1)
    (hscale2 : GeneratedCanonicalQM31 scale2)
    (hpoint0 : V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
      point0.val)
    (hpoint1 : V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
      point1.val)
    (hpoint2 : V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
      point2.val)
    (hpoint0Length : point0.val.length = 8)
    (hpoint1Length : point1.val.length = 8)
    (hpoint2Length : point2.val.length = 8)
    (halpha : GeneratedCanonicalQM31 alpha)
    (halpha2 : GeneratedCanonicalQM31 alpha2)
    (halpha3 : GeneratedCanonicalQM31 alpha3)
    (halpha2Exact : generatedQm31ToExact alpha2 =
      generatedQm31ToExact alpha ^ 2)
    (halpha3Exact : generatedQm31ToExact alpha3 =
      generatedQm31ToExact alpha ^ 3)
    (run0 : sumcheck.WeightAccumulator.impl.fold_multilinear_arity4
      scale0 point0 alpha alpha2 alpha3 = ok (scale0Out, point0Out))
    (run1 : sumcheck.WeightAccumulator.impl.fold_multilinear_arity4
      scale1 point1 alpha alpha2 alpha3 = ok (scale1Out, point1Out))
    (run2 : sumcheck.WeightAccumulator.impl.fold_multilinear_arity4
      scale2 point2 alpha alpha2 alpha3 = ok (scale2Out, point2Out)) :
    MultilinearFacts alpha scale0 scale1 scale2 point0 point1 point2
      scale0Out scale1Out scale2Out point0Out point1Out point2Out := by
  obtain ⟨hs0, hp0, hl0, hw0⟩ :=
    fold_multilinear_arity4_transports_weights scale0 point0 alpha alpha2
      alpha3 3 (by omega) (by omega) hscale0 hpoint0 halpha halpha2 halpha3
      halpha2Exact halpha3Exact scale0Out point0Out run0
  obtain ⟨hs1, hp1, hl1, hw1⟩ :=
    fold_multilinear_arity4_transports_weights scale1 point1 alpha alpha2
      alpha3 3 (by omega) (by omega) hscale1 hpoint1 halpha halpha2 halpha3
      halpha2Exact halpha3Exact scale1Out point1Out run1
  obtain ⟨hs2, hp2, hl2, hw2⟩ :=
    fold_multilinear_arity4_transports_weights scale2 point2 alpha alpha2
      alpha3 3 (by omega) (by omega) hscale2 hpoint2 halpha halpha2 halpha3
      halpha2Exact halpha3Exact scale2Out point2Out run2
  exact ⟨hs0, hs1, hs2, hp0, hp1, hp2, hl0, hl1, hl2, hw0, hw1, hw2⟩

private structure TensorFacts
    (alpha : RawQM31)
    (scale0 scale1 : RawQM31)
    (factors0 factors1 : alloc.vec.Vec RawQM31)
    (scale0Out scale1Out : RawQM31)
    (factors0Out factors1Out : alloc.vec.Vec RawQM31) : Prop where
  scale0Canonical : GeneratedCanonicalQM31 scale0Out
  scale1Canonical : GeneratedCanonicalQM31 scale1Out
  factors0Canonical :
    V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList factors0Out.val
  factors1Canonical :
    V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList factors1Out.val
  factors0Length : factors0Out.val.length = 6
  factors1Length : factors1Out.val.length = 6
  weights0 :
    AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 64 (exactRaw alpha)
        (structuredComponentWeights .tensor 4 scale0 factors0.val) =
      structuredComponentWeights .tensor 3 scale0Out factors0Out.val
  weights1 :
    AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 64 (exactRaw alpha)
        (structuredComponentWeights .tensor 4 scale1 factors1.val) =
      structuredComponentWeights .tensor 3 scale1Out factors1Out.val

private theorem tensor_facts
    (alpha alpha2 alpha3 : RawQM31)
    (preparedAlpha preparedAlpha2 : field.PreparedQm31Multiplier)
    (scale0 scale1 : RawQM31)
    (factors0 factors1 : alloc.vec.Vec RawQM31)
    (scale0Out scale1Out : RawQM31)
    (factors0Out factors1Out : alloc.vec.Vec RawQM31)
    (hscale0 : GeneratedCanonicalQM31 scale0)
    (hscale1 : GeneratedCanonicalQM31 scale1)
    (hfactors0 : V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList
      factors0.val)
    (hfactors1 : V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList
      factors1.val)
    (hfactors0Length : factors0.val.length = 8)
    (hfactors1Length : factors1.val.length = 8)
    (halpha : GeneratedCanonicalQM31 alpha)
    (halpha2 : GeneratedCanonicalQM31 alpha2)
    (halpha3 : GeneratedCanonicalQM31 alpha3)
    (hpreparedAlpha :
      V7CallerCurrentReleaseR26PreparedSumSemantics.RepresentsPrepared
        preparedAlpha alpha)
    (hpreparedAlpha2 :
      V7CallerCurrentReleaseR26PreparedSumSemantics.RepresentsPrepared
        preparedAlpha2 alpha2)
    (halpha2Exact : generatedQm31ToExact alpha2 =
      generatedQm31ToExact alpha ^ 2)
    (halpha3Exact : generatedQm31ToExact alpha3 =
      generatedQm31ToExact alpha ^ 3)
    (run0 : sumcheck.WeightAccumulator.impl.fold_tensor_arity4 scale0
      factors0 alpha3 preparedAlpha preparedAlpha2 =
        ok (scale0Out, factors0Out))
    (run1 : sumcheck.WeightAccumulator.impl.fold_tensor_arity4 scale1
      factors1 alpha3 preparedAlpha preparedAlpha2 =
        ok (scale1Out, factors1Out)) :
    TensorFacts alpha scale0 scale1 factors0 factors1 scale0Out scale1Out
      factors0Out factors1Out := by
  obtain ⟨hs0, hf0, hl0, hw0⟩ :=
    fold_tensor_arity4_transports_weights scale0 factors0 alpha alpha2 alpha3
      preparedAlpha preparedAlpha2 3 (by omega) (by omega) hscale0 hfactors0
      halpha halpha2 halpha3 hpreparedAlpha hpreparedAlpha2 halpha2Exact
      halpha3Exact scale0Out factors0Out run0
  obtain ⟨hs1, hf1, hl1, hw1⟩ :=
    fold_tensor_arity4_transports_weights scale1 factors1 alpha alpha2 alpha3
      preparedAlpha preparedAlpha2 3 (by omega) (by omega) hscale1 hfactors1
      halpha halpha2 halpha3 hpreparedAlpha hpreparedAlpha2 halpha2Exact
      halpha3Exact scale1Out factors1Out run1
  exact ⟨hs0, hs1, hf0, hf1, hl0, hl1, hw0, hw1⟩

private structure GroupedFacts
    (alpha0 alpha : RawQM31) (groupValues : alloc.vec.Vec RawQM31)
    (rowGroupsOut : alloc.vec.Vec Std.U8)
    (groupMasksOut : alloc.vec.Vec Std.U16)
    (firstAlphaOut : Option RawQM31)
    (groupValuesOut : alloc.vec.Vec RawQM31) : Type where
  power : ReleasedBinaryPowerTrace alpha0 alpha
  trace : ReleasedMaskValuesTrace
    (releasedBasis power.alpha0Cubed power.alpha0Squared alpha0
      power.cross alpha) power.total
  rowsExact : rowGroupsOut = releasedRowGroups64
  masksEmpty : groupMasksOut.val = []
  firstNone : firstAlphaOut = none
  valuesExact : groupValuesOut = releasedLowSevenValues
    trace.trace0.value trace.trace1.value trace.trace2.value trace.trace3.value
    trace.trace4.value trace.trace5.value trace.trace6.value
  lowSemantics : ReleasedLowValuesSemantics alpha0 alpha power trace
  weights :
    representedReleasedGroupedWeights releasedRowGroups64 groupValuesOut =
      AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 64
        (exactRaw alpha)
        (AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 256
          (exactRaw alpha0) releasedInactiveInitialWeight)

private theorem grouped_facts
    (alpha0 alpha alpha2 alpha3 : RawQM31)
    (groupValues : alloc.vec.Vec RawQM31)
    (rowGroupsOut : alloc.vec.Vec Std.U8)
    (groupMasksOut : alloc.vec.Vec Std.U16)
    (firstAlphaOut : Option RawQM31)
    (groupValuesOut : alloc.vec.Vec RawQM31)
    (halpha0 : GeneratedCanonicalQM31 alpha0)
    (halpha : GeneratedCanonicalQM31 alpha)
    (run :
      sumcheck.WeightAccumulator.impl.fold_grouped64_binary_deferred_arity4
        releasedRowGroups64 releasedMasks (some alpha0) groupValues 8#u32
        alpha alpha2 alpha3 =
          ok (rowGroupsOut, groupMasksOut, firstAlphaOut, groupValuesOut)) :
    Nonempty (GroupedFacts alpha0 alpha groupValues rowGroupsOut
      groupMasksOut firstAlphaOut groupValuesOut) := by
  obtain ⟨rowsExact, masksEmpty, firstNone, power, trace, valuesExact,
      lowSemantics, weights⟩ :=
    released_log8_success_corresponds alpha0 alpha alpha2 alpha3 groupValues
      rowGroupsOut groupMasksOut firstAlphaOut groupValuesOut halpha0 halpha run
  exact ⟨{
    power := power
    trace := trace
    rowsExact := rowsExact
    masksEmpty := masksEmpty
    firstNone := firstNone
    valuesExact := valuesExact
    lowSemantics := lowSemantics
    weights := weights }⟩

structure FirstFoldSevenSemantics
    (input output : sumcheck.WeightAccumulator) (alpha : RawQM31)
    (trace : FirstDeferredFoldTrace input alpha output)
    (mScale0 mScale1 mScale2 : RawQM31)
    (mPoint0 mPoint1 mPoint2 : alloc.vec.Vec RawQM31)
    (alpha0 : RawQM31) (groupValues : alloc.vec.Vec RawQM31)
    (tScale0 tScale1 : RawQM31)
    (tFactors0 tFactors1 : alloc.vec.Vec RawQM31)
    (lineScales : alloc.vec.Vec RawQM31)
    (lineXs : alloc.vec.Vec RawM31) : Type where
  source : FirstFoldSevenSourceTrace input alpha output trace
    mScale0 mScale1 mScale2 mPoint0 mPoint1 mPoint2 alpha0 groupValues
    tScale0 tScale1 tFactors0 tFactors1 lineScales lineXs
  mScale0Canonical : GeneratedCanonicalQM31 source.mScale0Out
  mScale1Canonical : GeneratedCanonicalQM31 source.mScale1Out
  mScale2Canonical : GeneratedCanonicalQM31 source.mScale2Out
  mPoint0Canonical :
    V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
      source.mPoint0Out.val
  mPoint1Canonical :
    V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
      source.mPoint1Out.val
  mPoint2Canonical :
    V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
      source.mPoint2Out.val
  mPoint0Length : source.mPoint0Out.val.length = 6
  mPoint1Length : source.mPoint1Out.val.length = 6
  mPoint2Length : source.mPoint2Out.val.length = 6
  multilinear0Weights :
    AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 64
        (exactRaw alpha)
        (structuredComponentWeights .multilinear 4 mScale0 mPoint0.val) =
      structuredComponentWeights .multilinear 3 source.mScale0Out
        source.mPoint0Out.val
  multilinear1Weights :
    AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 64
        (exactRaw alpha)
        (structuredComponentWeights .multilinear 4 mScale1 mPoint1.val) =
      structuredComponentWeights .multilinear 3 source.mScale1Out
        source.mPoint1Out.val
  multilinear2Weights :
    AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 64
        (exactRaw alpha)
        (structuredComponentWeights .multilinear 4 mScale2 mPoint2.val) =
      structuredComponentWeights .multilinear 3 source.mScale2Out
        source.mPoint2Out.val
  groupPower : ReleasedBinaryPowerTrace alpha0 alpha
  groupTrace : ReleasedMaskValuesTrace
    (releasedBasis groupPower.alpha0Cubed groupPower.alpha0Squared alpha0
      groupPower.cross alpha) groupPower.total
  groupRowsExact : source.rowGroupsOut = releasedRowGroups64
  groupMasksEmpty : source.groupMasksOut.val = []
  groupFirstNone : source.firstAlphaOut = none
  groupValuesExact : source.groupValuesOut = releasedLowSevenValues
    groupTrace.trace0.value groupTrace.trace1.value groupTrace.trace2.value
    groupTrace.trace3.value groupTrace.trace4.value groupTrace.trace5.value
    groupTrace.trace6.value
  groupLowSemantics : ReleasedLowValuesSemantics alpha0 alpha groupPower
    groupTrace
  groupedWeights :
    representedReleasedGroupedWeights releasedRowGroups64
        source.groupValuesOut =
      AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 64
        (exactRaw alpha)
        (AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 256
          (exactRaw alpha0) releasedInactiveInitialWeight)
  tScale0Canonical : GeneratedCanonicalQM31 source.tScale0Out
  tScale1Canonical : GeneratedCanonicalQM31 source.tScale1Out
  tFactors0Canonical :
    V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList
      source.tFactors0Out.val
  tFactors1Canonical :
    V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList
      source.tFactors1Out.val
  tFactors0Length : source.tFactors0Out.val.length = 6
  tFactors1Length : source.tFactors1Out.val.length = 6
  tensor0Weights :
    AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 64
        (exactRaw alpha)
        (structuredComponentWeights .tensor 4 tScale0 tFactors0.val) =
      structuredComponentWeights .tensor 3 source.tScale0Out
        source.tFactors0Out.val
  tensor1Weights :
    AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 64
        (exactRaw alpha)
        (structuredComponentWeights .tensor 4 tScale1 tFactors1.val) =
      structuredComponentWeights .tensor 3 source.tScale1Out
        source.tFactors1Out.val
  lineScalesCanonical : CanonicalQM31Slice source.lineScalesSliceOut
  lineXsCanonical : CanonicalM31Slice source.lineXsSliceOut
  lineScalesLength : source.lineScalesSliceOut.val.length = 16
  lineXsLength : source.lineXsSliceOut.val.length = 16
  lineDeferredExact : source.lineDeferredOut.val = 2
  lineBatchWeights :
    AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 64
        (exactRaw alpha)
        (lineBatchComponentWeights 4 (alloc.vec.Vec.deref lineScales)
          (alloc.vec.Vec.deref lineXs) 0) =
      lineBatchComponentWeights 3 source.lineScalesSliceOut
        source.lineXsSliceOut source.lineDeferredOut.val

theorem first_fold_seven_corresponds
    (input output : sumcheck.WeightAccumulator) (alpha : RawQM31)
    (trace : FirstDeferredFoldTrace input alpha output)
    (mScale0 mScale1 mScale2 : RawQM31)
    (mPoint0 mPoint1 mPoint2 : alloc.vec.Vec RawQM31)
    (alpha0 : RawQM31) (groupValues : alloc.vec.Vec RawQM31)
    (tScale0 tScale1 : RawQM31)
    (tFactors0 tFactors1 : alloc.vec.Vec RawQM31)
    (lineScales : alloc.vec.Vec RawQM31)
    (lineXs : alloc.vec.Vec RawM31)
    (hlog : input.log_len = 8#u32)
    (inputComponents : input.components.val =
      [.Multilinear mScale0 mPoint0,
       .Multilinear mScale1 mPoint1,
       .Multilinear mScale2 mPoint2,
       .Grouped64x16BinaryDeferred releasedRowGroups64 releasedMasks
         (some alpha0) groupValues,
       .Tensor tScale0 tFactors0,
       .Tensor tScale1 tFactors1,
       .LineM31Batch lineScales lineXs 0#u8])
    (halpha0 : GeneratedCanonicalQM31 alpha0)
    (halpha : GeneratedCanonicalQM31 alpha)
    (hmScale0 : GeneratedCanonicalQM31 mScale0)
    (hmScale1 : GeneratedCanonicalQM31 mScale1)
    (hmScale2 : GeneratedCanonicalQM31 mScale2)
    (hmPoint0 : V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
      mPoint0.val)
    (hmPoint1 : V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
      mPoint1.val)
    (hmPoint2 : V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
      mPoint2.val)
    (hmPoint0Length : mPoint0.val.length = 8)
    (hmPoint1Length : mPoint1.val.length = 8)
    (hmPoint2Length : mPoint2.val.length = 8)
    (htScale0 : GeneratedCanonicalQM31 tScale0)
    (htScale1 : GeneratedCanonicalQM31 tScale1)
    (htFactors0 : V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList
      tFactors0.val)
    (htFactors1 : V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList
      tFactors1.val)
    (htFactors0Length : tFactors0.val.length = 8)
    (htFactors1Length : tFactors1.val.length = 8)
    (hlineScalesLength : lineScales.val.length = 16)
    (hlineXsLength : lineXs.val.length = 16)
    (hlineScales : CanonicalQM31Slice (alloc.vec.Vec.deref lineScales))
    (hlineXs : CanonicalM31Slice (alloc.vec.Vec.deref lineXs)) :
    ∃ semantics : FirstFoldSevenSemantics input output alpha trace
      mScale0 mScale1 mScale2 mPoint0 mPoint1 mPoint2 alpha0 groupValues
      tScale0 tScale1 tFactors0 tFactors1 lineScales lineXs,
      True := by
  obtain ⟨source, _⟩ := first_fold_exposes_seven_source_components
    input alpha output trace mScale0 mScale1 mScale2 mPoint0 mPoint1 mPoint2
    alpha0 groupValues tScale0 tScale1 tFactors0 tFactors1 lineScales lineXs
    inputComponents
  have powers := trace.power_facts halpha
  have multilinear := multilinear_facts alpha trace.alphaSquared
    trace.alphaCubed mScale0 mScale1 mScale2 mPoint0 mPoint1 mPoint2
    source.mScale0Out source.mScale1Out source.mScale2Out source.mPoint0Out
    source.mPoint1Out source.mPoint2Out hmScale0 hmScale1 hmScale2 hmPoint0
    hmPoint1 hmPoint2 hmPoint0Length hmPoint1Length hmPoint2Length halpha
    powers.alphaSquaredCanonical powers.alphaCubedCanonical
    powers.alphaSquaredExact powers.alphaCubedExact source.multilinear0Run
    source.multilinear1Run source.multilinear2Run
  have groupedRun :
      sumcheck.WeightAccumulator.impl.fold_grouped64_binary_deferred_arity4
        releasedRowGroups64 releasedMasks (some alpha0) groupValues 8#u32
        alpha trace.alphaSquared trace.alphaCubed =
      ok (source.rowGroupsOut, source.groupMasksOut, source.firstAlphaOut,
        source.groupValuesOut) := by
    rw [← hlog]
    exact source.groupedRun
  obtain ⟨grouped⟩ := grouped_facts alpha0 alpha trace.alphaSquared
    trace.alphaCubed groupValues source.rowGroupsOut source.groupMasksOut
    source.firstAlphaOut source.groupValuesOut halpha0 halpha groupedRun
  have tensor := tensor_facts alpha trace.alphaSquared trace.alphaCubed
    trace.preparedAlpha trace.preparedAlphaSquared tScale0 tScale1 tFactors0
    tFactors1 source.tScale0Out source.tScale1Out source.tFactors0Out
    source.tFactors1Out htScale0 htScale1 htFactors0 htFactors1
    htFactors0Length htFactors1Length halpha powers.alphaSquaredCanonical
    powers.alphaCubedCanonical powers.preparedAlphaRepresents
    powers.preparedAlphaSquaredRepresents powers.alphaSquaredExact
    powers.alphaCubedExact source.tensor0Run source.tensor1Run
  have line := first_fold_line_facts alpha trace.alphaSquared trace.alphaCubed lineScales
    lineXs source.lineScalesSliceOut source.lineXsSliceOut
    source.lineDeferredOut hlineScalesLength hlineXsLength hlineScales hlineXs
    halpha powers.alphaSquaredCanonical powers.alphaCubedCanonical
    powers.alphaSquaredExact powers.alphaCubedExact source.lineBatchRun
  refine ⟨{
    source := source
    mScale0Canonical := multilinear.scale0Canonical
    mScale1Canonical := multilinear.scale1Canonical
    mScale2Canonical := multilinear.scale2Canonical
    mPoint0Canonical := multilinear.point0Canonical
    mPoint1Canonical := multilinear.point1Canonical
    mPoint2Canonical := multilinear.point2Canonical
    mPoint0Length := multilinear.point0Length
    mPoint1Length := multilinear.point1Length
    mPoint2Length := multilinear.point2Length
    multilinear0Weights := multilinear.weights0
    multilinear1Weights := multilinear.weights1
    multilinear2Weights := multilinear.weights2
    groupPower := grouped.power
    groupTrace := grouped.trace
    groupRowsExact := grouped.rowsExact
    groupMasksEmpty := grouped.masksEmpty
    groupFirstNone := grouped.firstNone
    groupValuesExact := grouped.valuesExact
    groupLowSemantics := grouped.lowSemantics
    groupedWeights := grouped.weights
    tScale0Canonical := tensor.scale0Canonical
    tScale1Canonical := tensor.scale1Canonical
    tFactors0Canonical := tensor.factors0Canonical
    tFactors1Canonical := tensor.factors1Canonical
    tFactors0Length := tensor.factors0Length
    tFactors1Length := tensor.factors1Length
    tensor0Weights := tensor.weights0
    tensor1Weights := tensor.weights1
    lineScalesCanonical := line.scalesCanonical
    lineXsCanonical := line.xsCanonical
    lineScalesLength := line.scalesLength
    lineXsLength := line.xsLength
    lineDeferredExact := line.deferredExact
    lineBatchWeights := line.weights }, trivial⟩

#print axioms first_fold_seven_corresponds

end V7CallerCurrentReleaseR26FirstFoldSevenSemantics

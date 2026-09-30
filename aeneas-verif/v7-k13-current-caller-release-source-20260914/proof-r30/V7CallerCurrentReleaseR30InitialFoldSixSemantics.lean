import V7CallerCurrentReleaseR30InitialFoldSixSource
import V7CallerCurrentReleaseR26MultilinearFoldSemantics
import V7CallerCurrentReleaseR26TensorFoldSemantics

/-!
# Symbolic semantics of the production initial six-component fold

This lifts the source trace for the log-ten fold to canonicality, dimensions,
and the exact log-eight component vector.  The grouped branch is the explicit
log-ten deferred branch, so it records the first alpha without evaluating a
large recurrence.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR30InitialFoldSixSemantics

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26WeightFoldLoopTrace
open V7CallerCurrentReleaseR26MultilinearFoldSemantics
open V7CallerCurrentReleaseR26TensorFoldSemantics
open V7CallerCurrentReleaseR30InitialFoldSixSource
open V7CallerCurrentReleaseR26PreparedSumSemantics

abbrev RawQM31 := field.QM31
abbrev RawPrepared := field.PreparedQm31Multiplier

private theorem multilinear_out_facts
    (scale : RawQM31) (point : alloc.vec.Vec RawQM31)
    (alpha alpha2 alpha3 scaleOut : RawQM31)
    (pointOut : alloc.vec.Vec RawQM31)
    (scaleCanonical : GeneratedCanonicalQM31 scale)
    (pointCanonical : V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
      point.val)
    (pointLength : point.val.length = 10)
    (alphaCanonical : GeneratedCanonicalQM31 alpha)
    (alpha2Canonical : GeneratedCanonicalQM31 alpha2)
    (alpha3Canonical : GeneratedCanonicalQM31 alpha3)
    (alpha2Exact : generatedQm31ToExact alpha2 =
      generatedQm31ToExact alpha ^ 2)
    (alpha3Exact : generatedQm31ToExact alpha3 =
      generatedQm31ToExact alpha ^ 3)
    (run : sumcheck.WeightAccumulator.impl.fold_multilinear_arity4
      scale point alpha alpha2 alpha3 = ok (scaleOut, pointOut)) :
    GeneratedCanonicalQM31 scaleOut ∧
      V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
        pointOut.val ∧ pointOut.val.length = 8 := by
  obtain ⟨expectedScale, expectedPoint, _factor, expectedRun,
      expectedScaleCanonical, expectedPointCanonical, pointExact, _⟩ :=
    fold_multilinear_arity4_exact scale point alpha alpha2 alpha3 8
      (by omega) (by omega) scaleCanonical pointCanonical alphaCanonical
      alpha2Canonical alpha3Canonical alpha2Exact alpha3Exact
  have outputExact : (scaleOut, pointOut) = (expectedScale, expectedPoint) :=
    Result.ok.inj (run.symm.trans expectedRun)
  cases outputExact
  refine ⟨expectedScaleCanonical, expectedPointCanonical, ?_⟩
  rw [pointExact]
  simp [pointLength]

private theorem tensor_out_facts
    (scale : RawQM31) (factors : alloc.vec.Vec RawQM31)
    (alpha alpha2 alpha3 scaleOut : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared)
    (factorsOut : alloc.vec.Vec RawQM31)
    (scaleCanonical : GeneratedCanonicalQM31 scale)
    (factorsCanonical : V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList
      factors.val)
    (factorsLength : factors.val.length = 10)
    (alphaCanonical : GeneratedCanonicalQM31 alpha)
    (alpha2Canonical : GeneratedCanonicalQM31 alpha2)
    (alpha3Canonical : GeneratedCanonicalQM31 alpha3)
    (preparedAlphaRepresents :
      V7CallerCurrentReleaseR26PreparedSumSemantics.RepresentsPrepared
        preparedAlpha alpha)
    (preparedAlpha2Represents :
      V7CallerCurrentReleaseR26PreparedSumSemantics.RepresentsPrepared
        preparedAlpha2 alpha2)
    (alpha2Exact : generatedQm31ToExact alpha2 =
      generatedQm31ToExact alpha ^ 2)
    (alpha3Exact : generatedQm31ToExact alpha3 =
      generatedQm31ToExact alpha ^ 3)
    (run : sumcheck.WeightAccumulator.impl.fold_tensor_arity4
      scale factors alpha3 preparedAlpha preparedAlpha2 =
        ok (scaleOut, factorsOut)) :
    GeneratedCanonicalQM31 scaleOut ∧
      V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList
        factorsOut.val ∧ factorsOut.val.length = 8 := by
  obtain ⟨expectedScale, expectedFactors, _factor, expectedRun,
      expectedScaleCanonical, expectedFactorsCanonical, factorsExact, _⟩ :=
    fold_tensor_arity4_exact scale factors alpha alpha2 alpha3 preparedAlpha
      preparedAlpha2 8 (by omega) (by omega) scaleCanonical factorsCanonical
      alphaCanonical alpha2Canonical alpha3Canonical preparedAlphaRepresents
      preparedAlpha2Represents alpha2Exact alpha3Exact
  have outputExact : (scaleOut, factorsOut) =
      (expectedScale, expectedFactors) :=
    Result.ok.inj (run.symm.trans expectedRun)
  cases outputExact
  refine ⟨expectedScaleCanonical, expectedFactorsCanonical, ?_⟩
  rw [factorsExact]
  simp [factorsLength]

private theorem grouped_log_ten_exact
    (inputLog : Std.U32)
    (rowGroups rowGroupsOut : alloc.vec.Vec Std.U8)
    (groupMasks groupMasksOut : alloc.vec.Vec Std.U16)
    (groupValues groupValuesOut : alloc.vec.Vec RawQM31)
    (firstAlphaOut : Option RawQM31)
    (alpha alpha2 alpha3 : RawQM31)
    (inputLogExact : inputLog = 10#u32)
    (run : sumcheck.WeightAccumulator.impl.fold_grouped64_binary_deferred_arity4
      rowGroups groupMasks none groupValues inputLog alpha alpha2 alpha3 =
        ok (rowGroupsOut, groupMasksOut, firstAlphaOut, groupValuesOut)) :
    (rowGroupsOut, groupMasksOut, firstAlphaOut, groupValuesOut) =
      (rowGroups, groupMasks, some alpha, groupValues) := by
  unfold sumcheck.WeightAccumulator.impl.fold_grouped64_binary_deferred_arity4 at run
  rw [inputLogExact] at run
  change ok (rowGroups, groupMasks, some alpha, groupValues) =
    ok (rowGroupsOut, groupMasksOut, firstAlphaOut, groupValuesOut) at run
  exact (Result.ok.inj run).symm

private theorem log_ten_folded :
    Std.U32.wrapping_sub 10#u32 2#u32 = 8#u32 := by
  apply UScalar.val_eq_imp
  rw [Std.U32.wrapping_sub_val_eq]
  norm_num [UScalar.size_def, UScalarTy.U32_numBits_eq]

structure InitialFoldSixSemantics
    (input : sumcheck.WeightAccumulator) (alpha : RawQM31)
    (output : sumcheck.WeightAccumulator)
    (trace : FirstDeferredFoldTrace input alpha output)
    (mScale0 mScale1 mScale2 : RawQM31)
    (mPoint0 mPoint1 mPoint2 : alloc.vec.Vec RawQM31)
    (rowGroups : alloc.vec.Vec Std.U8)
    (groupMasks : alloc.vec.Vec Std.U16)
    (groupValues : alloc.vec.Vec RawQM31)
    (tScale0 tScale1 : RawQM31)
    (tFactors0 tFactors1 : alloc.vec.Vec RawQM31) : Type where
  source : InitialFoldSixSourceTrace input alpha output trace
    mScale0 mScale1 mScale2 mPoint0 mPoint1 mPoint2 rowGroups groupMasks
    groupValues tScale0 tScale1 tFactors0 tFactors1
  outputLogLen : output.log_len = 8#u32
  outputComponents : output.components.val =
    [.Multilinear source.mScale0Out source.mPoint0Out,
     .Multilinear source.mScale1Out source.mPoint1Out,
     .Multilinear source.mScale2Out source.mPoint2Out,
     .Grouped64x16BinaryDeferred source.rowGroupsOut source.groupMasksOut
       source.firstAlphaOut source.groupValuesOut,
     .Tensor source.tScale0Out source.tFactors0Out,
     .Tensor source.tScale1Out source.tFactors1Out]
  mScale0Canonical : GeneratedCanonicalQM31 source.mScale0Out
  mScale1Canonical : GeneratedCanonicalQM31 source.mScale1Out
  mScale2Canonical : GeneratedCanonicalQM31 source.mScale2Out
  mPoint0Canonical : V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
    source.mPoint0Out.val
  mPoint1Canonical : V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
    source.mPoint1Out.val
  mPoint2Canonical : V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
    source.mPoint2Out.val
  mPoint0Length : source.mPoint0Out.val.length = 8
  mPoint1Length : source.mPoint1Out.val.length = 8
  mPoint2Length : source.mPoint2Out.val.length = 8
  groupExact : (source.rowGroupsOut, source.groupMasksOut,
      source.firstAlphaOut, source.groupValuesOut) =
    (rowGroups, groupMasks, some alpha, groupValues)
  tScale0Canonical : GeneratedCanonicalQM31 source.tScale0Out
  tScale1Canonical : GeneratedCanonicalQM31 source.tScale1Out
  tFactors0Canonical : V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList
    source.tFactors0Out.val
  tFactors1Canonical : V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList
    source.tFactors1Out.val
  tFactors0Length : source.tFactors0Out.val.length = 8
  tFactors1Length : source.tFactors1Out.val.length = 8

theorem initial_fold_six_corresponds
    (input : sumcheck.WeightAccumulator) (alpha : RawQM31)
    (output : sumcheck.WeightAccumulator)
    (trace : FirstDeferredFoldTrace input alpha output)
    (mScale0 mScale1 mScale2 : RawQM31)
    (mPoint0 mPoint1 mPoint2 : alloc.vec.Vec RawQM31)
    (rowGroups : alloc.vec.Vec Std.U8)
    (groupMasks : alloc.vec.Vec Std.U16)
    (groupValues : alloc.vec.Vec RawQM31)
    (tScale0 tScale1 : RawQM31)
    (tFactors0 tFactors1 : alloc.vec.Vec RawQM31)
    (inputLogLen : input.log_len = 10#u32)
    (inputComponents : input.components.val =
      [.Multilinear mScale0 mPoint0,
       .Multilinear mScale1 mPoint1,
       .Multilinear mScale2 mPoint2,
       .Grouped64x16BinaryDeferred rowGroups groupMasks none groupValues,
       .Tensor tScale0 tFactors0,
       .Tensor tScale1 tFactors1])
    (alphaCanonical : GeneratedCanonicalQM31 alpha)
    (mScale0Canonical : GeneratedCanonicalQM31 mScale0)
    (mScale1Canonical : GeneratedCanonicalQM31 mScale1)
    (mScale2Canonical : GeneratedCanonicalQM31 mScale2)
    (mPoint0Canonical : V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
      mPoint0.val)
    (mPoint1Canonical : V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
      mPoint1.val)
    (mPoint2Canonical : V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
      mPoint2.val)
    (mPoint0Length : mPoint0.val.length = 10)
    (mPoint1Length : mPoint1.val.length = 10)
    (mPoint2Length : mPoint2.val.length = 10)
    (tScale0Canonical : GeneratedCanonicalQM31 tScale0)
    (tScale1Canonical : GeneratedCanonicalQM31 tScale1)
    (tFactors0Canonical : V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList
      tFactors0.val)
    (tFactors1Canonical : V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList
      tFactors1.val)
    (tFactors0Length : tFactors0.val.length = 10)
    (tFactors1Length : tFactors1.val.length = 10) :
    Nonempty (InitialFoldSixSemantics input alpha output trace
      mScale0 mScale1 mScale2 mPoint0 mPoint1 mPoint2 rowGroups groupMasks
      groupValues tScale0 tScale1 tFactors0 tFactors1) := by
  obtain ⟨source, _⟩ := initial_fold_exposes_six_source_components input alpha
    output trace mScale0 mScale1 mScale2 mPoint0 mPoint1 mPoint2 rowGroups
    groupMasks groupValues tScale0 tScale1 tFactors0 tFactors1 inputComponents
  have powers := trace.power_facts alphaCanonical
  have m0 := multilinear_out_facts mScale0 mPoint0 alpha trace.alphaSquared
    trace.alphaCubed source.mScale0Out source.mPoint0Out mScale0Canonical
    mPoint0Canonical mPoint0Length alphaCanonical powers.alphaSquaredCanonical
    powers.alphaCubedCanonical powers.alphaSquaredExact powers.alphaCubedExact
    source.multilinear0Run
  have m1 := multilinear_out_facts mScale1 mPoint1 alpha trace.alphaSquared
    trace.alphaCubed source.mScale1Out source.mPoint1Out mScale1Canonical
    mPoint1Canonical mPoint1Length alphaCanonical powers.alphaSquaredCanonical
    powers.alphaCubedCanonical powers.alphaSquaredExact powers.alphaCubedExact
    source.multilinear1Run
  have m2 := multilinear_out_facts mScale2 mPoint2 alpha trace.alphaSquared
    trace.alphaCubed source.mScale2Out source.mPoint2Out mScale2Canonical
    mPoint2Canonical mPoint2Length alphaCanonical powers.alphaSquaredCanonical
    powers.alphaCubedCanonical powers.alphaSquaredExact powers.alphaCubedExact
    source.multilinear2Run
  have t0 := tensor_out_facts tScale0 tFactors0 alpha trace.alphaSquared
    trace.alphaCubed source.tScale0Out trace.preparedAlpha
    trace.preparedAlphaSquared source.tFactors0Out tScale0Canonical
    tFactors0Canonical tFactors0Length alphaCanonical powers.alphaSquaredCanonical
    powers.alphaCubedCanonical powers.preparedAlphaRepresents
    powers.preparedAlphaSquaredRepresents powers.alphaSquaredExact
    powers.alphaCubedExact source.tensor0Run
  have t1 := tensor_out_facts tScale1 tFactors1 alpha trace.alphaSquared
    trace.alphaCubed source.tScale1Out trace.preparedAlpha
    trace.preparedAlphaSquared source.tFactors1Out tScale1Canonical
    tFactors1Canonical tFactors1Length alphaCanonical powers.alphaSquaredCanonical
    powers.alphaCubedCanonical powers.preparedAlphaRepresents
    powers.preparedAlphaSquaredRepresents powers.alphaSquaredExact
    powers.alphaCubedExact source.tensor1Run
  have group := grouped_log_ten_exact input.log_len rowGroups source.rowGroupsOut
    groupMasks source.groupMasksOut groupValues source.groupValuesOut
    source.firstAlphaOut alpha trace.alphaSquared trace.alphaCubed inputLogLen
    source.groupedRun
  refine ⟨{
    source := source
    outputLogLen := by
      rw [trace.outputLogLen, inputLogLen]
      exact log_ten_folded
    outputComponents := source.output_components_exact
    mScale0Canonical := m0.1
    mScale1Canonical := m1.1
    mScale2Canonical := m2.1
    mPoint0Canonical := m0.2.1
    mPoint1Canonical := m1.2.1
    mPoint2Canonical := m2.2.1
    mPoint0Length := m0.2.2
    mPoint1Length := m1.2.2
    mPoint2Length := m2.2.2
    groupExact := group
    tScale0Canonical := t0.1
    tScale1Canonical := t1.1
    tFactors0Canonical := t0.2.1
    tFactors1Canonical := t1.2.1
    tFactors0Length := t0.2.2
    tFactors1Length := t1.2.2 }⟩

#print axioms initial_fold_six_corresponds

end V7CallerCurrentReleaseR30InitialFoldSixSemantics

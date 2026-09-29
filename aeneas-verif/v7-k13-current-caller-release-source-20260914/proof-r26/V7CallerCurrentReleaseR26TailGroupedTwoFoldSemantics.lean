import V7CallerCurrentReleaseR26TailTwoFoldSemantics
import V7CallerCurrentReleaseR26GroupedRowsTwiceSemantics

/-!
# K1 semantics of the fused tail's grouped component

The accepted tail dispatches the released 64-row grouped component to the
optimized `fold_grouped_rows_twice` helper.  This module connects that exact
dispatch result to the helper's maintained-field theorem and records the
four-row output component returned to the production accumulator.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TailGroupedTwoFoldSemantics

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26K1QueryWeightBridge
open V7CallerCurrentReleaseR26K1StructuredWeightBridge
open V7CallerCurrentReleaseR26TailWeightFoldTrace
open V7CallerCurrentReleaseR26TailSixDispatch
open V7CallerCurrentReleaseR26GroupedRows
open V7CallerCurrentReleaseR26GroupedRowsSemantics
open V7CallerCurrentReleaseR26GroupedRowsStaged
open V7CallerCurrentReleaseR26GroupedRowsTwiceSemantics

abbrev RawQM31 := field.QM31
abbrev Component := sumcheck.WeightComponent

structure TailGroupedSemantics
    {input : sumcheck.WeightAccumulator}
    {alphas : Array RawQM31 3#usize}
    {output : sumcheck.WeightAccumulator}
    (tail : AcceptedTailWeightFoldTrace input alphas output)
    (rowGroups : alloc.vec.Vec Std.U8)
    (groupMasks : alloc.vec.Vec Std.U16)
    (firstAlpha : Option RawQM31)
    (groupValues : alloc.vec.Vec RawQM31)
    (componentOut : Component) : Type where
  source : TailGroupedSourceTrace tail rowGroups groupMasks firstAlpha
    groupValues componentOut
  out0 : RawQM31
  out1 : RawQM31
  out2 : RawQM31
  out3 : RawQM31
  finalValuesCanonical : CanonicalFour out0 out1 out2 out3
  finalGroupsExact : source.foldedGroups = releasedRowGroups4
  finalValuesExact : source.foldedValues =
    releasedFourValues out0 out1 out2 out3
  outputExact : componentOut = .Grouped64x16BinaryDeferred
    releasedRowGroups4 groupMasks none
      (releasedFourValues out0 out1 out2 out3)
  outputWeights :
    representedGroupedWeights source.foldedGroups source.foldedValues =
      AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 4
        (exactRaw tail.alpha2)
        (AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 16
          (exactRaw tail.alpha1)
          (representedGroupedWeights rowGroups groupValues))

theorem tail_grouped_step_corresponds
    {input : sumcheck.WeightAccumulator}
    {alphas : Array RawQM31 3#usize}
    {output : sumcheck.WeightAccumulator}
    (tail : AcceptedTailWeightFoldTrace input alphas output)
    (rowGroups : alloc.vec.Vec Std.U8)
    (groupMasks : alloc.vec.Vec Std.U16)
    (firstAlpha : Option RawQM31)
    (groupValues : alloc.vec.Vec RawQM31)
    (componentOut : Component)
    (value0 value1 value2 value3 value4 value5 value6 : RawQM31)
    (rowsExact : rowGroups = releasedRowGroups64)
    (valuesExact : groupValues =
      releasedSevenValues value0 value1 value2 value3 value4 value5 value6)
    (valuesCanonical : CanonicalSeven value0 value1 value2 value3 value4
      value5 value6)
    (alpha1Canonical : GeneratedCanonicalQM31 tail.alpha1)
    (alpha2Canonical : GeneratedCanonicalQM31 tail.alpha2)
    (run : V7CallerCurrentReleaseR26TailComponentTrace.foldTailComponent
      alphas (Array.make 2#usize [tail.alpha1Squared, tail.alpha2Squared])
      (Array.make 2#usize [tail.preparedAlpha1, tail.preparedAlpha2])
      (Array.make 2#usize
        [tail.preparedAlpha1Squared, tail.preparedAlpha2Squared])
      (Array.make 2#usize [tail.alpha1Cubed, tail.alpha2Cubed])
      (.Grouped64x16BinaryDeferred rowGroups groupMasks firstAlpha
        groupValues) = ok (some componentOut)) :
    Nonempty (TailGroupedSemantics tail rowGroups groupMasks firstAlpha
      groupValues componentOut) := by
  obtain ⟨source⟩ := tail_grouped_step_exposes_source tail rowGroups
    groupMasks firstAlpha groupValues componentOut run
  have releasedRun : sumcheck.fold_grouped_rows_twice
      (alloc.vec.Vec.deref releasedRowGroups64)
      (alloc.vec.Vec.deref
        (releasedSevenValues value0 value1 value2 value3 value4 value5 value6))
      tail.alpha1 tail.alpha2 =
        ok (source.foldedGroups, source.foldedValues) := by
    simpa [rowsExact, valuesExact] using source.foldRun
  obtain ⟨out0, out1, out2, out3, groupsOut, valuesOut,
      outputsCanonical, weightsOut⟩ :=
    released_grouped_rows_twice_corresponds value0 value1 value2 value3
      value4 value5 value6 tail.alpha1 tail.alpha2 source.foldedGroups
      source.foldedValues valuesCanonical alpha1Canonical alpha2Canonical
      releasedRun
  refine ⟨{
    source := source
    out0 := out0
    out1 := out1
    out2 := out2
    out3 := out3
    finalValuesCanonical := outputsCanonical
    finalGroupsExact := groupsOut
    finalValuesExact := valuesOut
    outputExact := ?_
    outputWeights := ?_ }⟩
  · calc
      componentOut = .Grouped64x16BinaryDeferred source.foldedGroups
          groupMasks firstAlpha source.foldedValues := source.outputExact
      _ = .Grouped64x16BinaryDeferred releasedRowGroups4 groupMasks none
          (releasedFourValues out0 out1 out2 out3) := by
            rw [groupsOut, valuesOut, source.firstNone]
  · have inputWeightsExact :
        representedGroupedWeights (n := 64) rowGroups groupValues =
          representedGroupedWeights (n := 64) releasedRowGroups64
            (releasedSevenValues value0 value1 value2 value3 value4 value5
              value6) := by
      rw [rowsExact, valuesExact]
    rw [inputWeightsExact]
    exact weightsOut

#print axioms tail_grouped_step_corresponds

end V7CallerCurrentReleaseR26TailGroupedTwoFoldSemantics

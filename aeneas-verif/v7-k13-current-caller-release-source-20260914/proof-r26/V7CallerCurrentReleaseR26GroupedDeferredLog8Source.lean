import V7CallerCurrentReleaseR26GroupedLowTraceTotal
import V7CallerCurrentReleaseR26GroupedRows

/-!
# Exact source output of the released log-eight grouped helper

This isolates the generated branch calculation from its later K1 use so that
Lean does not elaborate the source unfolding under the larger semantic import
closure.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26GroupedDeferredLog8Source

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26GroupedFold
open V7CallerCurrentReleaseR26GroupedLowSemantics
open V7CallerCurrentReleaseR26GroupedLowTraceTotal
open V7CallerCurrentReleaseR26GroupedRows

abbrev RawQM31 := field.QM31

/-- Definitional equation for the generated log-eight branch, kept separate
from the semantic theorem so the elaborator never unfolds the other log cases
inside a large dependent goal. -/
theorem grouped_deferred_log8_branch
    (rowGroups : alloc.vec.Vec Std.U8)
    (groupMasks : alloc.vec.Vec Std.U16)
    (alpha0 : RawQM31) (groupValues : alloc.vec.Vec RawQM31)
    (alpha1 alpha2 alpha3 : RawQM31) :
    sumcheck.WeightAccumulator.impl.fold_grouped64_binary_deferred_arity4
        rowGroups groupMasks (some alpha0) groupValues 8#u32
          alpha1 alpha2 alpha3 =
      (do
        let groupValuesOut ←
          sumcheck.fold_binary_low_masks (alloc.vec.Vec.deref groupMasks)
            alpha0 alpha1
        let cleared ← alloc.vec.Vec.clear Global groupMasks
        ok (rowGroups, cleared, none, groupValuesOut)) := by
  convert
    (sumcheck.WeightAccumulator.impl.fold_grouped64_binary_deferred_arity4.eq_2
      rowGroups groupMasks (some alpha0) groupValues alpha1 alpha2 alpha3)
      using 1
  · congr 1
  · simp only [core.option.Option.take, core.option.Option.expect, ofOption,
      bind_tc_ok]

theorem released_log8_success_exposes_values
    (alpha0 alpha1 alpha2 alpha3 : RawQM31)
    (groupValues : alloc.vec.Vec RawQM31)
    (rowGroupsOut : alloc.vec.Vec Std.U8)
    (groupMasksOut : alloc.vec.Vec Std.U16)
    (firstAlphaOut : Option RawQM31)
    (groupValuesOut : alloc.vec.Vec RawQM31)
    (halpha0 : GeneratedCanonicalQM31 alpha0)
    (halpha1 : GeneratedCanonicalQM31 alpha1)
    (success :
      sumcheck.WeightAccumulator.impl.fold_grouped64_binary_deferred_arity4
          releasedRowGroups64 releasedMasks (some alpha0) groupValues
          8#u32 alpha1 alpha2 alpha3 =
        ok (rowGroupsOut, groupMasksOut, firstAlphaOut, groupValuesOut)) :
    ∃ (power : ReleasedBinaryPowerTrace alpha0 alpha1)
        (values : ReleasedMaskValuesTrace
          (releasedBasis power.alpha0Cubed power.alpha0Squared alpha0
            power.cross alpha1) power.total),
      rowGroupsOut = releasedRowGroups64 ∧
      groupMasksOut.val = [] ∧
      firstAlphaOut = none ∧
      groupValuesOut = releasedLowSevenValues
        values.trace0.value values.trace1.value values.trace2.value
        values.trace3.value values.trace4.value values.trace5.value
        values.trace6.value ∧
      ReleasedLowValuesSemantics alpha0 alpha1 power values := by
  obtain ⟨power, values, semantics, lowRun, valuesExact⟩ :=
    releasedLowSourceTrace_exists alpha0 alpha1 halpha0 halpha1
  have clearRun : alloc.vec.Vec.clear Global releasedMasks =
      ok (alloc.vec.Vec.new Std.U16) := by
    rfl
  have expected :
      sumcheck.WeightAccumulator.impl.fold_grouped64_binary_deferred_arity4
          releasedRowGroups64 releasedMasks (some alpha0) groupValues
          8#u32 alpha1 alpha2 alpha3 =
        ok (releasedRowGroups64, alloc.vec.Vec.new Std.U16, none,
          releasedLowSevenValues
            values.trace0.value values.trace1.value values.trace2.value
            values.trace3.value values.trace4.value values.trace5.value
            values.trace6.value) := by
    rw [grouped_deferred_log8_branch]
    rw [lowRun, clearRun]
    simp only [bind_tc_ok]
    exact congrArg
      (fun output : alloc.vec.Vec RawQM31 =>
        ok (releasedRowGroups64, alloc.vec.Vec.new Std.U16, none, output))
      valuesExact
  have same := Result.ok.inj (success.symm.trans expected)
  have rowsExact : rowGroupsOut = releasedRowGroups64 :=
    congrArg (fun output => output.1) same
  have masksExact : groupMasksOut = alloc.vec.Vec.new Std.U16 :=
    congrArg (fun output => output.2.1) same
  have firstExact : firstAlphaOut = none :=
    congrArg (fun output => output.2.2.1) same
  have valuesOutExact : groupValuesOut = releasedLowSevenValues
      values.trace0.value values.trace1.value values.trace2.value
      values.trace3.value values.trace4.value values.trace5.value
      values.trace6.value :=
    congrArg (fun output => output.2.2.2) same
  refine ⟨power, values, rowsExact, ?_, firstExact, valuesOutExact, semantics⟩
  rw [masksExact]

#print axioms released_log8_success_exposes_values

end V7CallerCurrentReleaseR26GroupedDeferredLog8Source

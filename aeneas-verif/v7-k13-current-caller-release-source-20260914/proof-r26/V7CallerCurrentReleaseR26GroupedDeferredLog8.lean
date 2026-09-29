import V7CallerCurrentReleaseR26GroupedDeferredLog8Source
import V7CallerCurrentReleaseR26GroupedInitialSemantics

/-!
# The released deferred grouped component at log length eight

The first source fold consumes the saved round-zero challenge together with
the current challenge.  This theorem identifies the exact compact state that
the generated helper returns and its maintained K1 meaning.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26GroupedDeferredLog8

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26GroupedFold
open V7CallerCurrentReleaseR26GroupedLowSemantics
open V7CallerCurrentReleaseR26GroupedLowTraceTotal
open V7CallerCurrentReleaseR26GroupedDeferredLog8Source
open V7CallerCurrentReleaseR26GroupedRows
open V7CallerCurrentReleaseR26GroupedInitialSemantics
open V7CallerCurrentReleaseR26K1StructuredWeightBridge

abbrev RawQM31 := field.QM31
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

/-- A successful log-eight source branch returns the released 64-row table,
an empty mask vector, no saved challenge, and seven values representing the
two K1 folds of the initial 1024-entry binary table. -/
theorem released_log8_success_corresponds
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
    rowGroupsOut = releasedRowGroups64 ∧
      groupMasksOut.val = [] ∧
      firstAlphaOut = none ∧
      ∃ (power : ReleasedBinaryPowerTrace alpha0 alpha1)
          (values : ReleasedMaskValuesTrace
            (releasedBasis power.alpha0Cubed power.alpha0Squared alpha0
              power.cross alpha1) power.total),
      groupValuesOut = releasedLowSevenValues
          values.trace0.value values.trace1.value values.trace2.value
          values.trace3.value values.trace4.value values.trace5.value
          values.trace6.value ∧
        ReleasedLowValuesSemantics alpha0 alpha1 power values ∧
        representedReleasedGroupedWeights releasedRowGroups64 groupValuesOut =
          AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 64
            (exactRaw alpha1)
            (AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 256
              (exactRaw alpha0) releasedInactiveInitialWeight) := by
  obtain ⟨power, values, rowsExact, masksEmpty, firstExact,
      valuesOutExact, semantics⟩ :=
    released_log8_success_exposes_values alpha0 alpha1 alpha2 alpha3
      groupValues rowGroupsOut groupMasksOut firstAlphaOut groupValuesOut
      halpha0 halpha1 success
  refine ⟨rowsExact, masksEmpty, firstExact, power, values, valuesOutExact,
    semantics, ?_⟩
  · rw [valuesOutExact]
    exact releasedLowValues_represent_foldedInactiveInitialWeight
      alpha0 alpha1 power values semantics

#print axioms released_log8_success_corresponds

end V7CallerCurrentReleaseR26GroupedDeferredLog8

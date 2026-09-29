import V7CallerCurrentReleaseR26FirstFoldMergeSource
import V7CallerCurrentReleaseR26FirstFoldSevenSemantics

/-!
# K1 semantics of the accepted post-first-fold merge

The production tail merges multilinear components zero and two only after its
generated vector comparison accepts their points.  This module proves that
comparison exact, transports the generated scale addition into K1, and states
the resulting component-weight equality.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26FirstFoldMergeSemantics

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26FirstFoldMergeSource
open V7CallerCurrentReleaseR26FirstFoldSevenOutput
open V7CallerCurrentReleaseR26FirstFoldSevenSemantics
open V7CallerCurrentReleaseR26K1QueryWeightBridge
open V7CallerCurrentReleaseR26K1StructuredWeightBridge
open V7CallerCurrentReleaseR26WeightFoldLoopTrace

abbrev RawQM31 := field.QM31
abbrev ModelQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

private theorem raw_qm31_eq_ok_true_iff_eq (left right : RawQM31) :
    field.QM31.Insts.CoreCmpPartialEqQM31.eq left right = .ok true ↔
      left = right := by
  rcases left with ⟨⟨left00, left01⟩, ⟨left10, left11⟩⟩
  rcases right with ⟨⟨right00, right01⟩, ⟨right10, right11⟩⟩
  by_cases h00 : left00 = right00 <;>
    by_cases h01 : left01 = right01 <;>
    by_cases h10 : left10 = right10 <;>
    by_cases h11 : left11 = right11 <;>
    simp_all [field.QM31.Insts.CoreCmpPartialEqQM31.eq,
      field.CM31.Insts.CoreCmpPartialEqCM31.eq,
      field.M31.Insts.CoreCmpPartialEqM31.eq]

private theorem allM_zip_raw_qm31_eq_true
    (left right : List RawQM31) (sameLength : left.length = right.length) :
    List.allM
        (fun pair =>
          field.QM31.Insts.CoreCmpPartialEqQM31.eq pair.1 pair.2)
        (List.zip left right) = .ok true →
      left = right := by
  induction left generalizing right with
  | nil =>
      intro run
      cases right <;> simp_all
  | cons head tail ih =>
      cases right with
      | nil => simp at sameLength
      | cons head' tail' =>
          intro run
          simp only [List.length_cons, Nat.add_right_cancel_iff] at sameLength
          simp only [List.zip_cons_cons, List.allM] at run
          generalize tailEquation : List.allM
              (fun pair =>
                field.QM31.Insts.CoreCmpPartialEqQM31.eq pair.1 pair.2)
              (List.zip tail tail') = tailResult at run
          cases headComparison :
              field.QM31.Insts.CoreCmpPartialEqQM31.eq head head' with
          | fail error => simp [headComparison] at run
          | div => simp [headComparison] at run
          | ok equal =>
              cases equal with
              | false =>
                  simp [headComparison] at run
                  cases Result.ok.inj run
              | true =>
                  have headExact : head = head' :=
                    (raw_qm31_eq_ok_true_iff_eq head head').mp headComparison
                  subst head'
                  simp [headComparison] at run
                  have tailExact := ih tail' sameLength
                    (run ▸ tailEquation)
                  subst tail'
                  rfl

/-- The exact generated vector comparison used by the merge cannot report
equality for distinct vectors. -/
theorem raw_qm31_vec_ne_false_implies_eq
    (left right : alloc.vec.Vec RawQM31) :
    Mut1A.Insts.CoreCmpPartialEqShared0B.ne
        (core.cmp.PartialEqVec field.QM31.Insts.CoreCmpPartialEqQM31)
        left right = .ok false →
      left = right := by
  intro run
  unfold Mut1A.Insts.CoreCmpPartialEqShared0B.ne at run
  unfold core.cmp.PartialEq.ne.trait_default at run
  unfold core.cmp.PartialEq.ne.default at run
  unfold core.cmp.PartialEqVec at run
  unfold alloc.vec.partial_eq.PartialEqVec.eq at run
  by_cases sameLength : left.val.length = right.val.length
  · simp only [sameLength, ↓reduceIte] at run
    generalize comparisonEquation : List.allM
        (fun pair =>
          field.QM31.Insts.CoreCmpPartialEqQM31.eq pair.1 pair.2)
        (List.zip left.val right.val) = comparison at run
    cases comparison with
    | fail error => simp at run
    | div => simp at run
    | ok equal =>
        cases equal <;> simp at run
        apply Subtype.ext
        exact allM_zip_raw_qm31_eq_true left.val right.val sameLength
          comparisonEquation
  · simp [sameLength] at run

structure FirstFoldMergeSemantics
    (afterFirst afterMerge : sumcheck.WeightAccumulator)
    (scale0 scale1 scale2 : RawQM31)
    (point0 point1 point2 : alloc.vec.Vec RawQM31)
    (grouped tensor0 tensor1 line : sumcheck.WeightComponent) : Type where
  source : FirstFoldMergeSourceTrace afterFirst afterMerge
    scale0 scale1 scale2 point0 point1 point2 grouped tensor0 tensor1 line
  pointsEqual : point0 = point2
  mergedScaleCanonical : GeneratedCanonicalQM31 source.mergedScale
  mergedScaleExact :
    generatedQm31ToExact source.mergedScale =
      generatedQm31ToExact scale0 + generatedQm31ToExact scale2
  mergedWeights :
    structuredComponentWeights .multilinear 3 source.mergedScale point0.val =
      fun index =>
        structuredComponentWeights .multilinear 3 scale0 point0.val index +
          structuredComponentWeights .multilinear 3 scale2 point2.val index

theorem accepted_merge_corresponds
    (afterFirst afterMerge : sumcheck.WeightAccumulator)
    (scale0 scale1 scale2 : RawQM31)
    (point0 point1 point2 : alloc.vec.Vec RawQM31)
    (grouped tensor0 tensor1 line : sumcheck.WeightComponent)
    (scale0Canonical : GeneratedCanonicalQM31 scale0)
    (scale2Canonical : GeneratedCanonicalQM31 scale2)
    (componentsExact : afterFirst.components.val =
      [.Multilinear scale0 point0,
       .Multilinear scale1 point1,
       .Multilinear scale2 point2,
       grouped, tensor0, tensor1, line])
    (run : sumcheck.WeightAccumulator.impl.merge_equal_multilinear_components
      afterFirst 0#usize 2#usize = ok (true, afterMerge)) :
    Nonempty (FirstFoldMergeSemantics afterFirst afterMerge
      scale0 scale1 scale2 point0 point1 point2 grouped tensor0 tensor1
      line) := by
  obtain ⟨source⟩ := accepted_merge_exposes_source afterFirst afterMerge
    scale0 scale1 scale2 point0 point1 point2 grouped tensor0 tensor1 line
    componentsExact run
  have pointsEqual : point0 = point2 :=
    raw_qm31_vec_ne_false_implies_eq point0 point2 source.pointsMatch
  obtain ⟨mergedScale, scaleRun, mergedScaleCanonical,
      mergedScaleExact⟩ :=
    generated_qm31_add_corresponds scale0 scale2 scale0Canonical
      scale2Canonical
  have mergedScaleEq : mergedScale = source.mergedScale := by
    exact Result.ok.inj (scaleRun.symm.trans source.scaleRun)
  subst mergedScale
  have mergedWeights :
      structuredComponentWeights .multilinear 3 source.mergedScale point0.val =
        fun index =>
          structuredComponentWeights .multilinear 3 scale0 point0.val index +
            structuredComponentWeights .multilinear 3 scale2 point2.val
              index := by
    subst point2
    funext index
    unfold structuredComponentWeights exactRaw
    rw [mergedScaleExact, sourceQm31ToModel_add]
    ring
  exact ⟨{
    source := source
    pointsEqual := pointsEqual
    mergedScaleCanonical := mergedScaleCanonical
    mergedScaleExact := mergedScaleExact
    mergedWeights := mergedWeights }⟩

/-- The exact seven-component first-fold theorem supplies the concrete input
vector and canonical scales required by the accepted merge theorem. -/
theorem first_fold_seven_then_merge_corresponds
    (input afterFirst afterMerge : sumcheck.WeightAccumulator)
    (alpha : RawQM31)
    (trace : FirstDeferredFoldTrace input alpha afterFirst)
    (mScale0 mScale1 mScale2 : RawQM31)
    (mPoint0 mPoint1 mPoint2 : alloc.vec.Vec RawQM31)
    (alpha0 : RawQM31) (groupValues : alloc.vec.Vec RawQM31)
    (tScale0 tScale1 : RawQM31)
    (tFactors0 tFactors1 : alloc.vec.Vec RawQM31)
    (lineScales : alloc.vec.Vec RawQM31)
    (lineXs : alloc.vec.Vec field.M31)
    (first : FirstFoldSevenSemantics input afterFirst alpha trace
      mScale0 mScale1 mScale2 mPoint0 mPoint1 mPoint2 alpha0 groupValues
      tScale0 tScale1 tFactors0 tFactors1 lineScales lineXs)
    (run : sumcheck.WeightAccumulator.impl.merge_equal_multilinear_components
      afterFirst 0#usize 2#usize = ok (true, afterMerge)) :
    Nonempty (FirstFoldMergeSemantics afterFirst afterMerge
      first.source.mScale0Out first.source.mScale1Out
      first.source.mScale2Out first.source.mPoint0Out
      first.source.mPoint1Out first.source.mPoint2Out
      (.Grouped64x16BinaryDeferred first.source.rowGroupsOut
        first.source.groupMasksOut first.source.firstAlphaOut
        first.source.groupValuesOut)
      (.Tensor first.source.tScale0Out first.source.tFactors0Out)
      (.Tensor first.source.tScale1Out first.source.tFactors1Out)
      (.LineM31Batch
        ((alloc.vec.Vec.deref_mut lineScales).2 first.source.lineScalesSliceOut)
        ((alloc.vec.Vec.deref_mut lineXs).2 first.source.lineXsSliceOut)
        first.source.lineDeferredOut)) := by
  apply accepted_merge_corresponds afterFirst afterMerge
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
    first.mScale0Canonical first.mScale2Canonical
  · exact
      V7CallerCurrentReleaseR26FirstFoldSevenOutput.FirstFoldSevenSourceTrace.output_components_exact
        first.source
  · exact run

#print axioms raw_qm31_vec_ne_false_implies_eq
#print axioms accepted_merge_corresponds
#print axioms first_fold_seven_then_merge_corresponds

end V7CallerCurrentReleaseR26FirstFoldMergeSemantics

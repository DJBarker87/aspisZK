import V7CallerCurrentReleaseR26FirstFoldSevenOutput
import V7CallerCurrentReleaseR26TailWeightFoldTrace

/-!
# Exact source result of the accepted post-first-fold merge

The production tail merges component two into component zero after the first
fold.  This module exposes the successful point comparison, scale addition,
and exact six-component output vector.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26FirstFoldMergeSource

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31
abbrev Component := sumcheck.WeightComponent

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do
      let value ← input
      next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

structure FirstFoldMergeSourceTrace
    (afterFirst afterMerge : sumcheck.WeightAccumulator)
    (scale0 scale1 scale2 : RawQM31)
    (point0 point1 point2 : alloc.vec.Vec RawQM31)
    (grouped tensor0 tensor1 line : Component) : Type where
  mergedScale : RawQM31
  pointsMatch :
    Mut1A.Insts.CoreCmpPartialEqShared0B.ne
      (core.cmp.PartialEqVec field.QM31.Insts.CoreCmpPartialEqQM31)
      point0 point2 = ok false
  scaleRun : field.QM31.add scale0 scale2 = ok mergedScale
  logExact : afterMerge.log_len = afterFirst.log_len
  componentsExact : afterMerge.components.val =
    [.Multilinear mergedScale point0,
     .Multilinear scale1 point1,
     grouped, tensor0, tensor1, line]

theorem accepted_merge_exposes_source
    (afterFirst afterMerge : sumcheck.WeightAccumulator)
    (scale0 scale1 scale2 : RawQM31)
    (point0 point1 point2 : alloc.vec.Vec RawQM31)
    (grouped tensor0 tensor1 line : Component)
    (componentsExact : afterFirst.components.val =
      [.Multilinear scale0 point0,
       .Multilinear scale1 point1,
       .Multilinear scale2 point2,
       grouped, tensor0, tensor1, line])
    (run : sumcheck.WeightAccumulator.impl.merge_equal_multilinear_components
      afterFirst 0#usize 2#usize = ok (true, afterMerge)) :
    Nonempty (FirstFoldMergeSourceTrace afterFirst afterMerge
      scale0 scale1 scale2 point0 point1 point2 grouped tensor0 tensor1
      line) := by
  unfold sumcheck.WeightAccumulator.impl.merge_equal_multilinear_components at run
  simp [componentsExact, alloc.vec.Vec.deref_mut, Slice.index_mut_usize,
    Slice.index_usize, core.slice.Slice.split_at_mut, Std.lift, bind_tc_ok]
    at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨pointsDiffer, pointsMatch, run⟩ := run
  cases pointsDiffer with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at run
      rw [bind_eq_ok_iff] at run
      obtain ⟨mergedScale, scaleRun, run⟩ := run
      simp [alloc.vec.Vec.remove] at run
      subst afterMerge
      exact ⟨{
        mergedScale := mergedScale
        pointsMatch := pointsMatch
        scaleRun := scaleRun
        logExact := rfl
        componentsExact := rfl }⟩
  | true => simp at run

#print axioms accepted_merge_exposes_source

end V7CallerCurrentReleaseR26FirstFoldMergeSource

import SumHighSingleRange
import SumHighModelCorrespondence
import SelectorMarginalModel
import R0P.Schedule

/-! Actual two-range sum_high execution. One accumulator crosses the range
boundary, as required by scheduleNodes; no reassociation of source calls. -/
set_option autoImplicit false
namespace AspisR1.SumHighTwoRanges
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.SumHighInnerLoop
open AspisR1.ExtractedMaskConstants
open AspisR1.ExtractedMaskQM31Exact
abbrev SliceIter := core.slice.iter.Iter Range
abbrev Outer := AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high_loop0

def pair (r s : Range) : Slice Range := Array.to_slice (Array.make 2#usize [r, s])
def iterAt (r s : Range) (i : Nat) : SliceIter := { slice := pair r s, i := i }

private theorem next_zero (r s : Range) :
    core.slice.iter.IteratorSliceIter.next (iterAt r s 0) = .ok (some r, iterAt r s 1) := by
  simp [iterAt, pair, core.slice.iter.IteratorSliceIter.next,
    Slice.len, Slice.length, Array.to_slice, Array.make]
private theorem next_one (r s : Range) :
    core.slice.iter.IteratorSliceIter.next (iterAt r s 1) = .ok (some s, iterAt r s 2) := by
  simp [iterAt, pair, core.slice.iter.IteratorSliceIter.next,
    Slice.len, Slice.length, Array.to_slice, Array.make]
private theorem next_two (r s : Range) :
    core.slice.iter.IteratorSliceIter.next (iterAt r s 2) = .ok (none, iterAt r s 2) := by
  simp [iterAt, pair, core.slice.iter.IteratorSliceIter.next,
    Slice.len, Slice.length, Array.to_slice, Array.make]

private theorem outer_done (r s : Range) (selectors : Selectors) (acc : QM) :
    Outer (iterAt r s 2) selectors acc = .ok acc := by
  change AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high_loop0
    (iterAt r s 2) selectors acc = .ok acc
  rw [AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high_loop0.eq_def]
  simp only [next_two, bind_tc_ok]

theorem pair_success (r s : Range) (selectors : Selectors)
    (hrstart : r.start.val ≤ r.end.val) (hrend : r.end.val ≤ 64)
    (hsstart : s.start.val ≤ s.end.val) (hsend : s.end.val ≤ 64)
    (hhigh : CanonicalArray selectors.high) :
    ∃ out, AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high
      selectors (pair r s) = .ok out ∧ Canonical out ∧
      decode out = sumModel selectors (s.end.val - s.start.val) s.start.val
        (sumModel selectors (r.end.val - r.start.val) r.start.val 0) := by
  obtain ⟨middle, hfirst, hcm, hvm⟩ := loop_model (r.end.val-r.start.val) r selectors
    field.QM31.ZERO hrend (by omega) hhigh zero_canonical
  obtain ⟨out, hsecond, hco, hvo⟩ := loop_model (s.end.val-s.start.val) s selectors
    middle hsend (by omega) hhigh hcm
  have hlast : Outer (iterAt r s 1) selectors middle = .ok out := by
    change AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high_loop0
      (iterAt r s 1) selectors middle = .ok out
    rw [AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high_loop0.eq_def]
    simp only [next_one, bind_tc_ok, AspisR1SumHighCandidate.clone_usize, hsecond, outer_done]
  refine ⟨out, ?_, hco, ?_⟩
  · unfold AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high
    simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, bind_tc_ok]
    change AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high_loop0
      (iterAt r s 0) selectors field.QM31.ZERO = .ok out
    rw [AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high_loop0.eq_def]
    simp only [next_zero, bind_tc_ok, AspisR1SumHighCandidate.clone_usize, hfirst, hlast]
  · rw [hvo, hvm, zero_decode]

theorem sumModel_acc (selectors : Selectors) (count start : Nat) (acc : AspisR1.SumHighInnerLoop.ExactQM) :
    sumModel selectors count start acc = acc + sumModel selectors count start 0 := by
  rw [AspisR1.SumHighModelCorrespondence.sumModel_eq_sum,
    AspisR1.SumHighModelCorrespondence.sumModel_eq_sum, zero_add]

def nodeRange1 : Range := { start := 4#usize, «end» := 25#usize }
def nodeRange2 : Range := { start := 33#usize, «end» := 57#usize }

attribute [local irreducible] R0P.g2High R0P.g2Low R0P.g2SumHigh

theorem scheduleNodes_two_sums {K : Type} [Field K] (sel : R0P.Sel K) :
    R0P.g2SumHigh sel 4 21 (by omega) + R0P.g2SumHigh sel 33 24 (by omega) =
      R0P.scheduleNodes sel := by
  simp only [R0P.scheduleNodes, R0P.g2SumHigh, R0P.g2_fold_add,
    List.sum_append, zero_add]

theorem boxed_nodes (point : Array QM 10#usize) (selectors : Selectors)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors) :
    ∃ out, AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high
      selectors (pair nodeRange1 nodeRange2) = .ok out ∧ Canonical out ∧
      decode out = R0P.scheduleNodes (AspisR1.SelectorValueLaneModelComposition.pointSelector point) := by
  obtain ⟨hhigh, _hlow, hhighModel, _hlowModel⟩ :=
    AspisR1.SelectorMarginalModel.boxed_marginals point selectors hpoint hbox
  obtain ⟨out, hrun, hco, hvo⟩ := pair_success nodeRange1 nodeRange2 selectors
    (by simp only [nodeRange1]; scalar_tac) (by simp only [nodeRange1]; scalar_tac)
    (by simp only [nodeRange2]; scalar_tac) (by simp only [nodeRange2]; scalar_tac) hhigh
  have h4 : (4#usize).val = 4 := by scalar_tac
  have h25 : (25#usize).val = 25 := by scalar_tac
  have h33 : (33#usize).val = 33 := by scalar_tac
  have h57 : (57#usize).val = 57 := by scalar_tac
  simp only [nodeRange1, nodeRange2, h4, h25, h33, h57] at hvo
  change decode out = sumModel selectors 24 33 (sumModel selectors 21 4 0) at hvo
  rw [sumModel_acc,
    AspisR1.SumHighModelCorrespondence.sumModel_eq_g2SumHigh selectors _ 24 33 (by omega) hhighModel,
    AspisR1.SumHighModelCorrespondence.sumModel_eq_g2SumHigh selectors _ 21 4 (by omega) hhighModel] at hvo
  refine ⟨out, hrun, hco, ?_⟩
  exact hvo.trans (scheduleNodes_two_sums _)

#print axioms pair_success
#print axioms sumModel_acc
#print axioms scheduleNodes_two_sums
#print axioms boxed_nodes
end
end AspisR1.SumHighTwoRanges

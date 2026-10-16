import SumHighGeneratedSlice
import OccupancyRangeTraversal
import SelectorExpansionCorrectness
import ExtractedMaskQM31Exact

/-! Actual shared sum_high inner loop: derive source success, retain the
unchanged selectors and implement the symbolic left-to-right field fold. -/
set_option autoImplicit false
namespace AspisR1.SumHighInnerLoop
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskQM31Exact

abbrev QM := field.QM31
abbrev Canonical := CurrentCanonicalQM
abbrev CanonicalArray {N : Usize} (a : Array QM N) :=
  AspisR1.SelectorExpansionCorrectness.canonicalArray a
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Range := core.ops.range.Range Usize
abbrev Loop := AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high_loop0_loop0
abbrev highAt (selectors : Selectors) :=
  AspisR1.SelectorExpansionCorrectness.decodedArray selectors.high

def sumModel (selectors : Selectors) : Nat → Nat → ExactQM → ExactQM
  | 0, _, acc => acc
  | n + 1, index, acc => sumModel selectors n (index + 1) (acc + highAt selectors index)

private theorem index_ok {α : Type} {N : Usize}
    (a : Array α N) (i : Usize) (hi : i.val < N.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

theorem readHigh_success (selectors : Selectors) (index : Usize)
    (hindex : index.val < 64) (hhigh : CanonicalArray selectors.high) :
    ∃ q, Array.index_usize selectors.high index = .ok q ∧ Canonical q ∧
      decode q = highAt selectors index.val := by
  let q := selectors.high.val[index.val]'(by simpa [selectors.high.property] using hindex)
  refine ⟨q, ?_, ?_, ?_⟩
  · exact index_ok selectors.high index (by simpa using hindex)
  · exact hhigh ⟨index.val, by simpa using hindex⟩
  · have hiBound : index.val < (64#usize).val := by scalar_tac
    simp only [highAt, AspisR1.SelectorExpansionCorrectness.decodedArray,
      AspisR1.SelectorExpansionCorrectness.decodedAt, dif_pos hiBound,
      AspisR1.SelectorExpansionCorrectness.decode]
    rfl

theorem loop_model
    (fuel : Nat) (iter : Range) (selectors : Selectors) (acc : QM)
    (hend : iter.end.val ≤ 64) (hspan : iter.start.val + fuel = iter.end.val)
    (hhigh : CanonicalArray selectors.high) (hacc : Canonical acc) :
    ∃ out, Loop iter selectors acc = .ok (selectors, out) ∧ Canonical out ∧
      decode out = sumModel selectors fuel iter.start.val (decode acc) := by
  induction fuel generalizing iter acc with
  | zero =>
      have hdone : iter.start.val ≥ iter.end.val := by omega
      refine ⟨acc, ?_, hacc, rfl⟩
      change AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high_loop0_loop0
        iter selectors acc = .ok (selectors, acc)
      rw [AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high_loop0_loop0.eq_def]
      simp only [AspisR1.OccupancyRangeTraversal.next_done iter hdone, bind_tc_ok]
  | succ fuel ih =>
      have hlt : iter.start.val < iter.end.val := by omega
      have hindex : iter.start.val < 64 := by omega
      obtain ⟨iter1, hnext, hstart1, hend1, _hbound⟩ :=
        AspisR1.OccupancyRangeTraversal.next_step iter hlt
      obtain ⟨q, hread, hcq, hvq⟩ := readHigh_success selectors iter.start hindex hhigh
      obtain ⟨acc1, hadd, hcacc1, hvacc1⟩ := current_qm_add_exact acc q hacc hcq
      obtain ⟨out, hrun, hcanonical, hmodel⟩ :=
        ih iter1 acc1 (by simpa only [hend1] using hend) (by rw [hend1, hstart1]; omega) hcacc1
      refine ⟨out, ?_, hcanonical, ?_⟩
      · change AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high_loop0_loop0
          iter selectors acc = .ok (selectors, out)
        rw [AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high_loop0_loop0.eq_def]
        simp only [hnext, bind_tc_ok, hread, hadd]
        exact hrun
      · rw [hmodel, hstart1, hvacc1, hvq]
        rfl

#print axioms readHigh_success
#print axioms loop_model
end
end AspisR1.SumHighInnerLoop

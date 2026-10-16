import SelectorValueLaneGeneratedSlice
import ExtractedMaskQM31Exact
import ExtractedMaskTowerAdd

/-! One recursive step of the actual `add_value_lanes_loop3` source. The
iterator read, field multiplication, and deferred writeback are kept in the
same order as the generated body. This is a step contract only; it does not
claim the completed 33-element traversal. -/
set_option autoImplicit false
namespace AspisR1.SelectorValueLaneLoop3Step

open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskTowerAdd
open AspisR1.ExtractedMaskQM31Exact

abbrev QM := field.QM31
abbrev IterMut := core.slice.iter.IterMut QM
abbrev Loop3 := pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop3

theorem add_value_lanes_loop3_step
    (iter : IterMut)
    (back : IterMut → IterMut)
    (rangeSelector : QM)
    (hhas : iter.i < iter.slice.len)
    (hselector : CanonicalQM rangeSelector)
    (hcell : CanonicalQM (iter.slice[iter.i])) :
    ∃ product : QM,
      Loop3 iter back rangeSelector =
        Loop3 { iter with i := iter.i + 1 }
          (fun im => back { im with slice := im.slice.setAtNat iter.i product })
          rangeSelector ∧
      CanonicalQM product ∧
      decode product = decode rangeSelector * decode (iter.slice[iter.i]) := by
  let residual : QM := iter.slice[iter.i]
  let iter1 : IterMut := { iter with i := iter.i + 1 }
  let nextBack : IterMut → Option QM → IterMut := fun it' x =>
    match x with
    | none => it'
    | some x => { it' with slice := it'.slice.setAtNat iter.i x }
  obtain ⟨product, hmul, hproduct, hdecode⟩ :=
    current_qm_mul_exact rangeSelector residual hselector (by simpa [residual] using hcell)
  have hnext :
      core.slice.iter.IteratorIterMut.next iter =
        .ok (some residual, iter1, nextBack) := by
    have hhas' : iter.i < iter.slice.val.length := by
      change iter.i < iter.slice.val.length at hhas
      exact hhas
    simp [core.slice.iter.IteratorIterMut.next, hhas', residual, iter1, nextBack]
    funext it' x
    cases x <;> rfl
  refine ⟨product, ?_, hproduct, ?_⟩
  · change pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop3
      iter back rangeSelector =
        pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop3
          { iter with i := iter.i + 1 }
          (fun im => back { im with slice := im.slice.setAtNat iter.i product })
          rangeSelector
    rw [pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop3.eq_def]
    simp only [hnext, bind_tc_ok, hmul, bind_tc_ok, nextBack, iter1]
  · simpa [residual] using hdecode

#print axioms add_value_lanes_loop3_step
end AspisR1.SelectorValueLaneLoop3Step

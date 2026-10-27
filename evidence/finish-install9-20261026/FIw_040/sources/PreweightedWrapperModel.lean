import PreweightedLoopCanonical
import PreweightedApplyGroups
import ExtractedMaskReducerOps

/-! Complete actual add_preweighted wrapper refinement: source execution,
canonicality and every packed cell equals its old value plus the exact
zero-padded four-lane contribution from the source interval. -/
set_option autoImplicit false
namespace AspisR1.PreweightedWrapperModel
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PreweightedClosureSuccess
open AspisR1.PreweightedGroupUpdate
open AspisR1.ExtractedMaskReducerOps
open AspisR1.PreweightedLoopModel
open AspisR1.PreweightedApplyGroups

theorem add_preweighted_model {N : Usize}
    (packed : Array QM 24#usize) (start : Usize) (values : Array QM N)
    (hn : 0 < N.val) (hinterval : start.val + N.val ≤ 96)
    (hpacked : CanonicalArray packed) (hvalues : CanonicalArray values) :
    ∃ out : Array QM 24#usize,
      AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted
        packed start values = .ok out ∧ CanonicalArray out ∧
      decoded out = (fun j => decoded packed j + groupValue values start.val j.val) := by
  have hmax : 96 ≤ Usize.max := by
    have h := Usize.cMax_bound_concrete.1
    omega
  have hdiv : (start / 4#usize : Result Usize) ⦃ z => z.val = start.val / 4 ⦄ := by
    apply Usize.div_spec
    decide
  obtain ⟨first, hfirst, hfirstVal⟩ := WP.spec_imp_exists hdiv
  have haddSpec : (start + N : Result Usize) ⦃ z => z.val = start.val + N.val ⦄ := by
    apply Usize.add_spec
    omega
  obtain ⟨ending, hending, hendingVal⟩ := WP.spec_imp_exists haddSpec
  obtain ⟨lastIndex, hsub, hlastIndex⟩ := sub_success ending 1#usize (by simp; omega)
  have hdivLast : (lastIndex / 4#usize : Result Usize) ⦃ z => z.val = lastIndex.val / 4 ⦄ := by
    apply Usize.div_spec
    decide
  obtain ⟨last, hlast, hlastVal⟩ := WP.spec_imp_exists hdivLast
  let iter : core.ops.range.RangeInclusive Usize := ⟨first, last, false⟩
  have hnew : core.ops.range.RangeInclusive.new first last = .ok iter := rfl
  have hone : (1#usize).val = 1 := by scalar_tac
  have hlastIndexNat : lastIndex.val = ending.val - 1 := by simpa only [hone] using hlastIndex
  have hlastBound : last.val < 24 := by omega
  obtain ⟨out, hrun, hcanon, hmodel⟩ := AspisR1.PreweightedLoopModel.loop_model
    iter packed start values hlastBound hinterval hpacked hvalues
  have hlastNat : last.val = (start.val + N.val - 1) / 4 := by
    rw [hlastVal, hlastIndexNat, hendingVal]
  have hfirstLast : first.val ≤ last.val := by omega
  have hremaining : remaining iter = last.val - first.val + 1 := by
    simp only [remaining, iter, Bool.false_eq_true, false_or]
    rw [if_neg (by omega)]
  have hclosed : decoded out =
      (fun j => decoded packed j + groupValue values start.val j.val) := by
    rw [hmodel]
    funext j
    rw [applyGroups_cell]
    change decoded packed j +
      (if first.val ≤ j.val ∧ j.val < first.val + remaining iter
       then groupValue values start.val j.val else 0) =
      decoded packed j + groupValue values start.val j.val
    by_cases hin : first.val ≤ j.val ∧ j.val < first.val + remaining iter
    · rw [if_pos hin]
    · rw [if_neg hin]
      have hout : j.val < start.val / 4 ∨ (start.val + N.val - 1) / 4 < j.val := by
        rw [hremaining] at hin
        omega
      rw [groupValue_outside values start.val j.val hn hout]
  refine ⟨out, ?_, hcanon, hclosed⟩
  unfold AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted
  change (do
    let first' ← UScalar.div start 4#usize
    let ending' ← UScalar.add start N
    let lastIndex' ← UScalar.sub ending' 1#usize
    let last' ← UScalar.div lastIndex' 4#usize
    let iter' ← core.ops.range.RangeInclusive.new first' last'
    AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted_loop
      iter' packed start values) = .ok out
  change UScalar.div start 4#usize = .ok first at hfirst
  change UScalar.add start N = .ok ending at hending
  change UScalar.div lastIndex 4#usize = .ok last at hlast
  rw [hfirst]
  simp only [bind_tc_ok]
  rw [hending]
  simp only [bind_tc_ok]
  rw [hsub]
  simp only [bind_tc_ok]
  rw [hlast]
  simp only [bind_tc_ok]
  rw [hnew]
  simp only [bind_tc_ok]
  exact hrun

#print axioms add_preweighted_model
end AspisR1.PreweightedWrapperModel

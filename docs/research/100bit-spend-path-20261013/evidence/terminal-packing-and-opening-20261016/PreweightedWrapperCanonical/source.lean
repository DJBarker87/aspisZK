import PreweightedLoopCanonical
import ExtractedMaskReducerOps

/-! Actual add_preweighted wrapper success and canonicality, including checked
interval arithmetic and inclusive-iterator construction. -/
set_option autoImplicit false
namespace AspisR1.PreweightedWrapperCanonical
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PreweightedClosureSuccess
open AspisR1.PreweightedGroupUpdate
open AspisR1.ExtractedMaskReducerOps

theorem add_preweighted_success {N : Usize}
    (packed : Array QM 24#usize) (start : Usize) (values : Array QM N)
    (hn : 0 < N.val) (hinterval : start.val + N.val ≤ 96)
    (hpacked : CanonicalArray packed) (hvalues : CanonicalArray values) :
    ∃ out : Array QM 24#usize,
      AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted
        packed start values = .ok out ∧ CanonicalArray out := by
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
  obtain ⟨out, hrun, hcanon⟩ := AspisR1.PreweightedLoopCanonical.loop_success
    iter packed start values hlastBound hinterval hpacked hvalues
  refine ⟨out, ?_, hcanon⟩
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

#print axioms add_preweighted_success
end AspisR1.PreweightedWrapperCanonical

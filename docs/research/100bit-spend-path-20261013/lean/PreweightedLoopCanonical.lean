import PreweightedGroupUpdate
import Aeneas.Std.RangeIter

/-! Termination and canonicality for the actual inclusive-range traversal.
The per-group source arithmetic is supplied by the proved concrete theorem,
not an external callback premise. Exact lane-value composition is separate. -/
set_option autoImplicit false
namespace AspisR1.PreweightedLoopCanonical
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PreweightedClosureSuccess
open AspisR1.PreweightedGroupUpdate

private def remaining (r : core.ops.range.RangeInclusive Usize) : Nat :=
  if r.exhausted = true ∨ r.«end».val < r.start.val then 0
  else r.«end».val - r.start.val + 1

theorem loop_success {N : Usize}
    (r : core.ops.range.RangeInclusive Usize) (packed : Array QM 24#usize)
    (start : Usize) (values : Array QM N)
    (hend : r.«end».val < 24) (hinterval : start.val + N.val ≤ 96)
    (hpacked : CanonicalArray packed) (hvalues : CanonicalArray values) :
    ∃ out : Array QM 24#usize,
      AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted_loop
        r packed start values = .ok out ∧ CanonicalArray out := by
  generalize hcount : remaining r = count
  induction count using Nat.strong_induction_on generalizing r packed with
  | h count ih =>
      obtain ⟨pair, hnext, hpost⟩ := WP.spec_imp_exists
        (core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next_Usize_spec r)
      rcases pair with ⟨o, r'⟩
      by_cases hempty : r.exhausted = true ∨ r.«end».val < r.start.val
      · simp only [if_pos hempty] at hpost
        rcases hpost with ⟨rfl, rfl⟩
        refine ⟨packed, ?_, hpacked⟩
        rw [generated_loop_step]
        simp only [hnext, bind_tc_ok]
      · have hstart : r.start.val ≤ r.«end».val := by omega
        have hgroup : r.start.val < 24 := by omega
        obtain ⟨updated, hupdate, hcanonical, hvalue, hframe⟩ :=
          runGroup_success packed r.start start values hgroup hinterval hpacked hvalues
        by_cases hlt : r.start.val < r.«end».val
        · simp only [if_neg hempty, if_pos hlt] at hpost
          rcases hpost with ⟨rfl, hstep, hend', hexhausted⟩
          have hremain : remaining r' < count := by
            rw [← hcount]
            unfold remaining
            simp only [if_neg hempty, hexhausted, Bool.false_eq_true, false_or, hend']
            rw [if_neg (by omega)]
            omega
          obtain ⟨out, hrun, hcanon⟩ := ih (remaining r') hremain r' updated
            (by simpa [hend'] using hend) hcanonical rfl
          refine ⟨out, ?_, hcanon⟩
          rw [generated_loop_step]
          simp only [hnext, bind_tc_ok, hupdate, bind_tc_ok, hrun]
        · simp only [if_neg hempty, if_neg hlt] at hpost
          rcases hpost with ⟨rfl, hsame, hend', hexhausted⟩
          have hremain : remaining r' < count := by
            rw [← hcount]
            unfold remaining
            simp only [hexhausted, true_or, if_true, if_neg hempty]
            omega
          obtain ⟨out, hrun, hcanon⟩ := ih (remaining r') hremain r' updated
            (by simpa [hend'] using hend) hcanonical rfl
          refine ⟨out, ?_, hcanon⟩
          rw [generated_loop_step]
          simp only [hnext, bind_tc_ok, hupdate, bind_tc_ok, hrun]

#print axioms loop_success
end AspisR1.PreweightedLoopCanonical

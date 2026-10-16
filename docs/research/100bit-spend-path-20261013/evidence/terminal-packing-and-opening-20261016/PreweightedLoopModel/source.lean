import PreweightedLoopCanonical

/-! Exact mathematical state transformer for the actual packed-group traversal.
No concrete traversal is normalized; the proof follows the symbolic group
count and consumes the checked source read/pack/add/write theorem. -/
set_option autoImplicit false
namespace AspisR1.PreweightedLoopModel
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PreweightedClosureSuccess
open AspisR1.PreweightedGroupUpdate
open AspisR1.ExtractedMaskQM31Exact

abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev State := Fin 24 → ExactQM

def decoded (packed : Array QM 24#usize) : State := fun j =>
  decode (packed.val[j.val]'(by simpa [packed.property] using j.isLt))

def groupValue {N : Usize} (values : Array QM N) (start group : Nat) : ExactQM :=
  AspisR1.ExtractedMaskQmPackBase4Arithmetic.mathematicalPack
    (fun j : Fin 4 => selectedCell values start group j.val)

def step {N : Usize} (values : Array QM N) (start group : Nat) (a : State) : State :=
  fun j => if j.val = group then a j + groupValue values start group else a j

def applyGroups {N : Usize} (values : Array QM N) (start : Nat) : Nat → Nat → State → State
  | 0, _, a => a
  | n + 1, group, a => applyGroups values start n (group + 1) (step values start group a)

theorem runGroup_model {N : Usize}
    (packed : Array QM 24#usize) (group start : Usize) (values : Array QM N)
    (hgroup : group.val < 24) (hinterval : start.val + N.val ≤ 96)
    (hpacked : CanonicalArray packed) (hvalues : CanonicalArray values) :
    ∃ updated : Array QM 24#usize,
      runGroup packed group start values = .ok updated ∧
      CanonicalArray updated ∧
      decoded updated = step values start.val group.val (decoded packed) := by
  obtain ⟨updated, hrun, hcanon, hvalue, hframe⟩ :=
    runGroup_success packed group start values hgroup hinterval hpacked hvalues
  refine ⟨updated, hrun, hcanon, ?_⟩
  funext j
  unfold decoded step
  by_cases hj : j.val = group.val
  · rw [if_pos hj]
    simpa [hj, groupValue] using hvalue
  · rw [if_neg hj, hframe j hj]

def remaining (r : core.ops.range.RangeInclusive Usize) : Nat :=
  if r.exhausted = true ∨ r.«end».val < r.start.val then 0
  else r.«end».val - r.start.val + 1

/-- The actual generated outer loop computes the symbolic packed-array state
transformer on every canonical input, including the exhausted/empty cases. -/
theorem loop_model {N : Usize}
    (r : core.ops.range.RangeInclusive Usize) (packed : Array QM 24#usize)
    (start : Usize) (values : Array QM N)
    (hend : r.«end».val < 24) (hinterval : start.val + N.val ≤ 96)
    (hpacked : CanonicalArray packed) (hvalues : CanonicalArray values) :
    ∃ out : Array QM 24#usize,
      AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted_loop
        r packed start values = .ok out ∧ CanonicalArray out ∧
      decoded out = applyGroups values start.val (remaining r) r.start.val (decoded packed) := by
  generalize hcount : remaining r = count
  induction count using Nat.strong_induction_on generalizing r packed with
  | h count ih =>
      obtain ⟨pair, hnext, hpost⟩ := WP.spec_imp_exists
        (core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next_Usize_spec r)
      rcases pair with ⟨o, r'⟩
      by_cases hempty : r.exhausted = true ∨ r.«end».val < r.start.val
      · simp only [if_pos hempty] at hpost
        rcases hpost with ⟨rfl, rfl⟩
        have hz : count = 0 := by simpa [remaining, hempty] using hcount.symm
        refine ⟨packed, ?_, hpacked, ?_⟩
        · rw [generated_loop_step]
          simp only [hnext, bind_tc_ok]
        · simp [hz, applyGroups]
      · have hstart : r.start.val ≤ r.«end».val := by omega
        have hgroup : r.start.val < 24 := by omega
        obtain ⟨updated, hupdate, hcanonical, hmodel⟩ :=
          runGroup_model packed r.start start values hgroup hinterval hpacked hvalues
        by_cases hlt : r.start.val < r.«end».val
        · simp only [if_neg hempty, if_pos hlt] at hpost
          rcases hpost with ⟨rfl, hstep, hend', hexhausted⟩
          have hremaining : remaining r' + 1 = count := by
            rw [← hcount]
            unfold remaining
            simp only [if_neg hempty, hexhausted, Bool.false_eq_true, false_or, hend']
            rw [if_neg (by omega)]
            omega
          have hdecrease : remaining r' < count := by omega
          obtain ⟨out, hrun, hcanon, hdecode⟩ := ih (remaining r') hdecrease r' updated
            (by simpa [hend'] using hend) hcanonical rfl
          refine ⟨out, ?_, hcanon, ?_⟩
          · rw [generated_loop_step]
            simp only [hnext, bind_tc_ok, hupdate, bind_tc_ok, hrun]
          · rw [hdecode, ← hremaining, applyGroups, hmodel, hstep]
        · simp only [if_neg hempty, if_neg hlt] at hpost
          rcases hpost with ⟨rfl, hsame, hend', hexhausted⟩
          have hremaining : remaining r' = 0 := by simp [remaining, hexhausted]
          have hcountOne : count = 1 := by
            rw [← hcount]
            unfold remaining
            rw [if_neg hempty]
            omega
          obtain ⟨out, hrun, hcanon, hdecode⟩ := ih 0 (by omega) r' updated
            (by simpa [hend'] using hend) hcanonical hremaining
          refine ⟨out, ?_, hcanon, ?_⟩
          · rw [generated_loop_step]
            simp only [hnext, bind_tc_ok, hupdate, bind_tc_ok, hrun]
          · simpa [applyGroups, hcountOne] using hdecode.trans hmodel

#print axioms runGroup_model
#print axioms loop_model
end AspisR1.PreweightedLoopModel

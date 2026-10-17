import AspisR1.CopyPatternLimbExact
import AspisR1.ResultBindSequence

/-! Factor the exact source recursion through its checked lane body. -/
set_option autoImplicit false
namespace AspisR1.CopyPatternLoopFactor
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.CopyPatternLimbExact
abbrev Loop := AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop1_loop0
abbrev Width := AspisR1CopyPatternCandidate.poseidon2.POSEIDON2_WIDTH

theorem loop_step_eq (openings powers : Array QM 16#usize) (limb : Usize)
    (pattern : Pattern) (value : QM) (hlt : limb < Width) :
    Loop openings powers limb pattern value = (do
      let value1 ← runLimb openings powers limb pattern value
      let limb1 ← limb + 1#usize
      Loop openings powers limb1 pattern value1) := by
  unfold Loop
  rw [AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop1_loop0.eq_def,
    if_pos hlt]
  unfold runLimb
  cases hread : Array.index_usize pattern.kinds limb with
  | fail err => rfl
  | div => rfl
  | ok kind =>
    simp only [bind_tc_ok]
    by_cases hk : kind = 1#u8
    · simp only [if_pos hk, ← AspisR1.ResultBindSequence.group_first]
    · simp only [if_neg hk,bind_tc_ok]

#print axioms loop_step_eq
end AspisR1.CopyPatternLoopFactor

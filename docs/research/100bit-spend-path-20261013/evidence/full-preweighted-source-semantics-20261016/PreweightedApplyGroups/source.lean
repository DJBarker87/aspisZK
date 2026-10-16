import PreweightedLoopModel

/-! Closed form for the symbolic packed-group state transformer. This avoids
normalizing any concrete traversal when connecting the source loop to the
semantic lane map. -/
set_option autoImplicit false
namespace AspisR1.PreweightedApplyGroups
open Aeneas Aeneas.Std
open AspisR1.PreweightedClosureSuccess
open AspisR1.PreweightedLoopModel

theorem applyGroups_cell {N : Usize} (values : Array QM N) (start n first : Nat)
    (a : State) (j : Fin 24) :
    applyGroups values start n first a j = a j +
      (if first ≤ j.val ∧ j.val < first + n then groupValue values start j.val else 0) := by
  induction n generalizing first a with
  | zero =>
      have hempty : ¬ (first ≤ j.val ∧ j.val < first + 0) := by omega
      simp [applyGroups, hempty]
  | succ n ih =>
      rw [applyGroups, ih]
      by_cases heq : j.val = first
      · have hfuture : ¬ (first + 1 ≤ j.val ∧ j.val < first + 1 + n) := by omega
        have hcurrent : first ≤ j.val ∧ j.val < first + (n + 1) := by omega
        rw [if_neg hfuture]
        simp only [step, if_pos heq]
        rw [if_pos hcurrent]
        simp only [add_zero, heq]
      · have hsame : (first + 1 ≤ j.val ∧ j.val < first + 1 + n) ↔
            (first ≤ j.val ∧ j.val < first + (n + 1)) := by omega
        simp only [step, if_neg heq, hsame]

/-- Outside the groups touched by a nonempty source interval, all four
source-selected lanes are zero, so their packed contribution is zero. -/
theorem groupValue_outside {N : Usize} (values : Array QM N)
    (start group : Nat) (hn : 0 < N.val)
    (hout : group < start / 4 ∨ (start + N.val - 1) / 4 < group) :
    groupValue values start group = 0 := by
  have hcell (j : Fin 4) : selectedCell values start group j.val =
      AspisR1SelectedMaskProbe.field.QM31.ZERO := by
    unfold selectedCell
    rw [if_neg (by rcases hout with h | h <;> omega)]
  have hfun : (fun j : Fin 4 => selectedCell values start group j.val) =
      (fun _ : Fin 4 => AspisR1SelectedMaskProbe.field.QM31.ZERO) := by
    funext j
    exact hcell j
  unfold groupValue
  rw [hfun]
  simp only [AspisR1.ExtractedMaskQmPackBase4Arithmetic.mathematicalPack,
    AspisR1.ExtractedMaskConstants.zero_decode, mul_zero, add_zero]

#print axioms groupValue_outside
#print axioms applyGroups_cell
end AspisR1.PreweightedApplyGroups

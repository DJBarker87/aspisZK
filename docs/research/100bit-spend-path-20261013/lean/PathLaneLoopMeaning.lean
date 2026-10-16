import PathLaneSourceLoop

/-! Closed form for disjoint paired path writes. This symbolic lemma replaces
any normalization of the eight-step source recurrence. -/
set_option autoImplicit false
namespace AspisR1.PathLaneLoopMeaning
noncomputable section
attribute [local instance] Classical.propDecidable
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PathLaneSourceStep
open AspisR1.PathLaneSourceLoop

private def leftWritten (start count j : Nat) : Prop :=
  1 ≤ j ∧ j < 9 ∧ start ≤ j - 1 ∧ j - 1 < start + count
private def rightWritten (start count j : Nat) : Prop :=
  9 ≤ j ∧ j < 17 ∧ start ≤ j - 9 ∧ j - 9 < start + count

/-- Each traversed lane writes two distinct cells, and no later iteration
can overwrite them. The proof is symbolic in both start and count. -/
theorem applySteps_cell
    (selector bit : QM) (a a1 : Array QM 16#usize)
    (count start : Nat) (s : State) (hbound : start + count ≤ 8) (j : Fin 17) :
    applySteps selector bit a a1 count start s j =
      if leftWritten start count j.val then left selector bit a a1 (j.val - 1)
      else if rightWritten start count j.val then right selector bit a a1 (j.val - 9)
      else s j := by
  classical
  induction count generalizing start s with
  | zero =>
      have hl : ¬ leftWritten start 0 j.val := by unfold leftWritten; omega
      have hr : ¬ rightWritten start 0 j.val := by unfold rightWritten; omega
      simp only [applySteps, if_neg hl, if_neg hr]
  | succ count ih =>
      rw [applySteps, ih (start + 1) (step selector bit a a1 start s) (by omega)]
      by_cases hl : leftWritten (start + 1) count j.val
      · have hL : leftWritten start (count + 1) j.val := by
          unfold leftWritten at *; omega
        simp only [if_pos hl, if_pos hL]
      · by_cases hr : rightWritten (start + 1) count j.val
        · have hR : rightWritten start (count + 1) j.val := by
            unfold rightWritten at *; omega
          have hL : ¬ leftWritten start (count + 1) j.val := by
            unfold leftWritten rightWritten at *; omega
          simp only [if_neg hl, if_pos hr, if_neg hL, if_pos hR]
        · simp only [if_neg hl, if_neg hr, step]
          by_cases hj : j.val = 1 + start
          · have hL : leftWritten start (count + 1) j.val := by
              unfold leftWritten; omega
            have hindex : j.val - 1 = start := by omega
            simp only [if_pos hj, if_pos hL, hindex]
          · by_cases hjR : j.val = 9 + start
            · have hL : ¬ leftWritten start (count + 1) j.val := by
                unfold leftWritten; omega
              have hR : rightWritten start (count + 1) j.val := by
                unfold rightWritten; omega
              have hindex : j.val - 9 = start := by omega
              simp only [if_neg hj, if_pos hjR, if_neg hL, if_pos hR, hindex]
            · have hL : ¬ leftWritten start (count + 1) j.val := by
                unfold leftWritten at *; omega
              have hR : ¬ rightWritten start (count + 1) j.val := by
                unfold rightWritten at *; omega
              simp only [if_neg hj, if_neg hjR, if_neg hL, if_neg hR]

/-- The complete loop preserves cell0 and writes exactly the eight left and
right residuals; no field recurrence or concrete loop is unfolded. -/
theorem applySteps_from_zero
    (selector bit : QM) (a a1 : Array QM 16#usize) (s : State) :
    (applySteps selector bit a a1 8 0 s) 0 = s 0 ∧
    (∀ i : Fin 8, (applySteps selector bit a a1 8 0 s)
      ⟨1 + i.val, by omega⟩ = left selector bit a a1 i.val) ∧
    (∀ i : Fin 8, (applySteps selector bit a a1 8 0 s)
      ⟨9 + i.val, by omega⟩ = right selector bit a a1 i.val) := by
  constructor
  · rw [applySteps_cell selector bit a a1 8 0 s (by omega) 0]
    simp [leftWritten, rightWritten]
  · constructor
    · intro i
      rw [applySteps_cell selector bit a a1 8 0 s (by omega)]
      have hl : leftWritten 0 8 (1 + i.val) := by unfold leftWritten; have := i.isLt; omega
      simp only [if_pos hl]
      congr 1
      omega
    · intro i
      rw [applySteps_cell selector bit a a1 8 0 s (by omega)]
      have hl : ¬ leftWritten 0 8 (9 + i.val) := by unfold leftWritten; omega
      have hr : rightWritten 0 8 (9 + i.val) := by unfold rightWritten; have := i.isLt; omega
      simp only [if_neg hl, if_pos hr]
      congr 1
      omega

#print axioms applySteps_cell
#print axioms applySteps_from_zero
end
end AspisR1.PathLaneLoopMeaning

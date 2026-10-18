import CompPolyFactorMeanTools

set_option pp.all true
noncomputable section
namespace AspisR1.CompPolyFactorTwoChildBound
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1.CompPolyFactorMeanTools
variable {I A X : Type} [Fintype A] [Nonempty A]

theorem append_abort_mean (p : Program I A (Option (List X))) (left : List X) :
    outMean (bind p (fun right => match right with
      | none => .done none
      | some r => .done (some (left++r)))) abortIndicator = outMean p abortIndicator := by
  rw [outMean_bind]
  apply outMean_congr
  intro o
  cases o <;> rfl

/-- Conditional on a successful split, the two recursive computations can
abort only within the sum of their individual abort budgets. -/
theorem two_children_abort_le (left right : Program I A (Option (List X)))
    (BL BR : ℚ) (hBR : 0 ≤ BR)
    (hl : outMean left abortIndicator ≤ BL) (hr : outMean right abortIndicator ≤ BR) :
    outMean (bind left (fun leftResult => match leftResult with
      | none => .done none
      | some l => bind right (fun rightResult => match rightResult with
        | none => .done none
        | some r => .done (some (l++r))))) abortIndicator ≤ BL+BR := by
  have hnext : ∀ l : List X,
      outMean (bind right (fun rightResult => match rightResult with
        | none => .done none
        | some r => .done (some (l++r)))) abortIndicator ≤ BR := by
    intro l
    rw [append_abort_mean]
    exact hr
  exact (bind_abort_le left _ BR hBR hnext).trans (add_le_add hl (le_refl BR))

#print axioms append_abort_mean
#print axioms two_children_abort_le
end AspisR1.CompPolyFactorTwoChildBound

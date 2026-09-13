import Mathlib.Tactic

/-! S5 FIRST ATTEMPT, UNCOMPILED. Arithmetic of the buffered source control
pattern. Instantiating actual sampler traces with these bounds is still a source
proof, not a premise that may be renamed as a closed global bound. -/
set_option autoImplicit false
namespace AspisV8Completion.FSV8S5BufferedAccounting

theorem bounded_trial_sum : ∀ (trials : List Nat),
    (∀ n ∈ trials, n ≤ 8) → trials.sum ≤ 8*trials.length := by
  intro trials
  induction trials with
  | nil => simp
  | cons n rest ih =>
      intro bounded
      have hn := bounded n (by simp)
      have hr := ih (fun m hm => bounded m (by simp [hm]))
      simp only [List.sum_cons,List.length_cons]
      omega

theorem ordinary_buffered_calls_le_eight (trials : List Nat)
    (limbs : trials.length ≤ 4) (bounded : ∀ n ∈ trials, n ≤ 8) :
    2*((trials.sum+7)/8) ≤ 8 := by
  have hs := bounded_trial_sum trials bounded
  omega

/-- Includes optional positive descriptor and the point-claims query. All
ordinary/nonzero/circle constants must first be bound to actual source traces. -/
theorem complete_selected_numeric_budget :
    (24*8+24+18) + 1 + (123+53+9) = 420 := by omega

theorem complete_selected_budget_fits : 420 ≤ 1511 := by omega

/-- Adding conservative Script indices does NOT fit the old root allocation. -/
theorem coarse_script_indices_do_not_fit : 1511 < 1800+1+1403 := by omega

#print axioms bounded_trial_sum
#print axioms ordinary_buffered_calls_le_eight
#print axioms complete_selected_numeric_budget
end AspisV8Completion.FSV8S5BufferedAccounting

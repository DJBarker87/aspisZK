import Mathlib
set_option autoImplicit false
namespace AspisR1.SecondFoldBudgetTest
private theorem sum_range_sq_mul_six (m : Nat) :
    (∑ j ∈ Finset.range m, j ^ 2) * 6 = m * (m - 1) * (2 * m - 1) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [Finset.sum_range_succ]
      by_cases hm : m = 0
      · subst m
        norm_num
      · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
        have hsub : m - 1 + 1 = m := Nat.sub_add_cancel hm1
        have hs : m + 1 - 1 = m := by omega
        have htwo : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
        rw [hs, htwo]
        nlinarith [ih, hsub]
end AspisR1.SecondFoldBudgetTest

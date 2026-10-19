import Mathlib.Data.Nat.Basic
import Init.Data.Nat.Log2
import Lean.Elab.Tactic.Omega

namespace ExtractorPowComplexity

def rawPowModMulCount : Nat → Nat
  | 0 => 0
  | n + 1 => 1 + (if (n + 1) % 2 = 1 then 1 else 0) + rawPowModMulCount ((n + 1) / 2)

theorem rawPowModMulCount_le_log_bound (n : Nat) :
    rawPowModMulCount n ≤ 2 * (Nat.log2 n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp [rawPowModMulCount]
      | succ m =>
          by_cases hm : m = 0
          · subst m
            simp [rawPowModMulCount, Nat.log2_def]
          · have hsmall : 2 ≤ m + 1 := by omega
            have hrec : (m + 1) / 2 < m + 1 :=
              Nat.div_lt_self (by omega) (by decide)
            have hi := ih ((m + 1) / 2) hrec
            rw [rawPowModMulCount, Nat.log2_def]
            simp only [if_pos hsmall]
            have hbit : (if (m + 1) % 2 = 1 then 1 else 0) ≤ 1 := by
              split <;> omega
            omega

#print axioms rawPowModMulCount_le_log_bound

end ExtractorPowComplexity

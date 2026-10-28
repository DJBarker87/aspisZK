import R1Z.CommitReadsR1

/-! The R1 privacy error at N = 8 under the binary-multiproof read budget
`115 + Mc ≤ 2^22` (`CommitReadsR1.mc_le`; r1p-readbudget/READ-BUDGET-BINARY.md).

The privacy theorems (`privacy_R1`, `privacy_R1_games′` /
`privacy_R1_games_spendSampler`, `privacy_R1P`) are parametric in the read
count (`M`, `Mc`, `N * n1 W Pr`); their statements are unchanged.  This module
evaluates their error expressions at the new constant:

* `r1_error_N8_bin`: the D41 form (`zkfs_R1_abort_N8`, three terms, `M = Mi =
  8 · 2^22`, `q = 2^64`, `Umin = 2^255`, exhaustion slot `2^-250`) is
  `≤ 2^-165` (it was `≤ 2^-166` at `8 · 2^21`).
* `exh_bin_le`: the body of `FinalR1P.εexhP 8 L₁ L₂ M` under `RCommitCount`
  and `M ≤ 8 · 2^22` is `≤ 2^-229`.
* `r1_games_error_le`: the error expression of `privacy_R1_games_spendSampler`
  (D42.1 form with the pole term, `Mi = 0`) at `N = 8`, for every `Mc` with
  `115 + Mc ≤ 2^22`, `qmax ≤ 2^64` and `εexh ≤ 2^-229`, is
  `≤ 2^-109 + 2^-137`: the pole term `8 · 4096 / (p⁴ − 1)` dominates.
* `r1_games_error_RCommitCount`: the same at `Mc = McR1 (2 L₁) (2 L₂)`. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ReadBudgetR1
open R1Z.CommitReadsR1

/-- D41 form at the binary budget: `M = Mi = 8 · 2^22`. -/
theorem r1_error_N8_bin :
    ((8 * 2 ^ 22 : ℕ) : ℚ) * ((2 ^ 64 : ℕ) : ℚ) / ((2 ^ 255 : ℕ) : ℚ) +
      (((8 * 2 ^ 22 : ℕ) : ℚ) * ((8 * 2 ^ 22 : ℕ) : ℚ) / ((2 ^ 255 : ℕ) : ℚ) +
        (1 / 2 ^ 250 : ℚ)) +
      ((8 * 2 ^ 22 : ℕ) : ℚ) * ((8 * 2 ^ 22 : ℕ) : ℚ) / ((2 ^ 255 : ℕ) : ℚ) ≤
    1 / 2 ^ 165 := by
  norm_num

/-- The exhaustion slot of `FinalR1P.εexhP` at `N = 8`. -/
theorem exh_bin_le (L₁ L₂ M : ℕ) (hc : RCommitCount L₁ L₂) (hM : M ≤ 8 * 2 ^ 22) :
    ((8 : ℕ) : ℚ) * (16 * (L₁ + L₂)) / 2 ^ 496 + (M : ℚ) * (1 / 2 ^ 255) ≤ 1 / 2 ^ 229 := by
  obtain ⟨h1, h2⟩ := hc
  have hL : ((L₁ + L₂ : ℕ) : ℚ) ≤ 49152 := by
    have : L₁ + L₂ ≤ 49152 := by omega
    exact_mod_cast this
  have hM' : (M : ℚ) ≤ 8 * 2 ^ 22 := by exact_mod_cast hM
  push_cast at hL
  calc ((8 : ℕ) : ℚ) * (16 * (L₁ + L₂)) / 2 ^ 496 + (M : ℚ) * (1 / 2 ^ 255)
      ≤ (8 : ℚ) * (16 * 49152) / 2 ^ 496 + (8 * 2 ^ 22 : ℚ) * (1 / 2 ^ 255) := by
        push_cast
        gcongr
    _ ≤ 1 / 2 ^ 229 := by
        -- `2^496` is past the numeral evaluator's exponent limit (256): split it.
        rw [show (2 : ℚ) ^ 496 = 2 ^ 248 * 2 ^ 248 by rw [← pow_add]]
        norm_num

/-- The pole term at `N = 8`. -/
theorem pole_N8 : (8 : ℚ) * ((4096 : ℚ) / (((2 ^ 31 - 1) ^ 4 - 1 : ℕ) : ℚ)) ≤
    1 / 2 ^ 109 + 1 / 2 ^ 138 + 1 / 2 ^ 160 := by
  norm_num

/-- The error of `privacy_R1_games_spendSampler` at `N = 8` under the binary
read budget. -/
theorem r1_games_error_le (Mc qmax : ℕ) (εexh : ℚ) (hM : 115 + Mc ≤ 2 ^ 22)
    (hq : qmax ≤ 2 ^ 64) (he : εexh ≤ 1 / 2 ^ 229) :
    ((8 * (115 + Mc) : ℕ) : ℚ) * (qmax : ℚ) / ((2 ^ 255 : ℕ) : ℚ) +
        (((8 * (115 + Mc) : ℕ) : ℚ) * ((8 * (115 + Mc) : ℕ) : ℚ) / ((2 ^ 255 : ℕ) : ℚ) + εexh) +
        ((0 : ℕ) : ℚ) * ((0 : ℕ) : ℚ) / ((2 ^ 255 : ℕ) : ℚ) +
        (8 : ℚ) * ((4096 : ℚ) / (((2 ^ 31 - 1) ^ 4 - 1 : ℕ) : ℚ)) ≤
      1 / 2 ^ 109 + 1 / 2 ^ 137 := by
  have hA : ((8 * (115 + Mc) : ℕ) : ℚ) ≤ 8 * 2 ^ 22 := by
    have : 8 * (115 + Mc) ≤ 8 * 2 ^ 22 := by omega
    exact_mod_cast this
  have hA0 : (0 : ℚ) ≤ ((8 * (115 + Mc) : ℕ) : ℚ) := Nat.cast_nonneg _
  have hq' : (qmax : ℚ) ≤ 2 ^ 64 := by exact_mod_cast hq
  have hq0 : (0 : ℚ) ≤ qmax := Nat.cast_nonneg _
  have hU : (0 : ℚ) < ((2 ^ 255 : ℕ) : ℚ) := by positivity
  have h1 : ((8 * (115 + Mc) : ℕ) : ℚ) * (qmax : ℚ) / ((2 ^ 255 : ℕ) : ℚ) ≤
      (8 * 2 ^ 22 : ℚ) * 2 ^ 64 / ((2 ^ 255 : ℕ) : ℚ) := by
    gcongr
  have h2 : ((8 * (115 + Mc) : ℕ) : ℚ) * ((8 * (115 + Mc) : ℕ) : ℚ) / ((2 ^ 255 : ℕ) : ℚ) ≤
      (8 * 2 ^ 22 : ℚ) * (8 * 2 ^ 22) / ((2 ^ 255 : ℕ) : ℚ) := by
    gcongr
  have hp := pole_N8
  have hz : ((0 : ℕ) : ℚ) * ((0 : ℕ) : ℚ) / ((2 ^ 255 : ℕ) : ℚ) = 0 := by simp
  rw [hz]
  have hnum : (8 * 2 ^ 22 : ℚ) * 2 ^ 64 / ((2 ^ 255 : ℕ) : ℚ) +
      ((8 * 2 ^ 22 : ℚ) * (8 * 2 ^ 22) / ((2 ^ 255 : ℕ) : ℚ) + 1 / 2 ^ 229) + 0 +
      (1 / 2 ^ 109 + 1 / 2 ^ 138 + 1 / 2 ^ 160) ≤ 1 / 2 ^ 109 + 1 / 2 ^ 137 := by
    norm_num
  linarith

/-- The same at the source count `Mc = McR1 (2 L₁) (2 L₂)` (`mc_le`). -/
theorem r1_games_error_RCommitCount (L₁ L₂ qmax : ℕ) (εexh : ℚ) (hc : RCommitCount L₁ L₂)
    (hq : qmax ≤ 2 ^ 64) (he : εexh ≤ 1 / 2 ^ 229) :
    ((8 * (115 + McR1 (2 * L₁) (2 * L₂)) : ℕ) : ℚ) * (qmax : ℚ) / ((2 ^ 255 : ℕ) : ℚ) +
        (((8 * (115 + McR1 (2 * L₁) (2 * L₂)) : ℕ) : ℚ) *
            ((8 * (115 + McR1 (2 * L₁) (2 * L₂)) : ℕ) : ℚ) / ((2 ^ 255 : ℕ) : ℚ) + εexh) +
        ((0 : ℕ) : ℚ) * ((0 : ℕ) : ℚ) / ((2 ^ 255 : ℕ) : ℚ) +
        (8 : ℚ) * ((4096 : ℚ) / (((2 ^ 31 - 1) ^ 4 - 1 : ℕ) : ℚ)) ≤
      1 / 2 ^ 109 + 1 / 2 ^ 137 :=
  r1_games_error_le _ qmax εexh (mc_le L₁ L₂ hc) hq he

end R1Z.ReadBudgetR1

#print axioms R1Z.ReadBudgetR1.r1_error_N8_bin
#print axioms R1Z.ReadBudgetR1.exh_bin_le
#print axioms R1Z.ReadBudgetR1.pole_N8
#print axioms R1Z.ReadBudgetR1.r1_games_error_le
#print axioms R1Z.ReadBudgetR1.r1_games_error_RCommitCount

import R1Z.CertLiftBasic
import AspisFormal.CircleNaturalBasisEval

/-! D59.2: the builder's bit-by-bit natural-basis evaluation (`natR`, the
extracted `nat_loop` = basis.rs `natural`) is the Lean `naturalLineValue`
(`∏_{b ∈ bits(m)} D_b(x)`) on every index below `2^k` (`natR_eq`), so the
D53.2 item "natural against naturalLineValue" is a lemma, not a premise. -/

set_option autoImplicit false

namespace R1Z.CertBuild
open AspisCircleTensorBinding
open scoped BigOperators

variable {K : Type} [Field K]

theorem df_succ (x : K) : ∀ b : ℕ, doubledFactor x (b + 1) = doubledFactor (x * x + x * x - 1) b
  | 0 => by simp [doubledFactor]; ring
  | b + 1 => by rw [doubledFactor, df_succ x b, doubledFactor]

theorem nlv_even (x : K) (n : ℕ) :
    naturalLineValue x (2 * n) = naturalLineValue (x * x + x * x - 1) n := by
  unfold naturalLineValue
  rw [List.prod_toFinset _ Nat.bitIndices_nodup, List.prod_toFinset _ Nat.bitIndices_nodup,
    Nat.bitIndices_two_mul, List.map_map]
  congr 1
  exact List.map_congr_left fun b _ => df_succ x b

theorem nlv_odd (x : K) (n : ℕ) :
    naturalLineValue x (2 * n + 1) = x * naturalLineValue (x * x + x * x - 1) n := by
  unfold naturalLineValue
  rw [List.prod_toFinset _ Nat.bitIndices_nodup, List.prod_toFinset _ Nat.bitIndices_nodup,
    Nat.bitIndices_two_mul_add_one, List.map_cons, List.prod_cons, List.map_map]
  congr 1
  congr 1
  exact List.map_congr_left fun b _ => df_succ x b

theorem natR_eq (x : K) : ∀ (k m : ℕ), m < 2 ^ k → natR x m k = naturalLineValue x m
  | 0, m, hm => by
      have : m = 0 := by simpa using hm
      subst this
      simp [natR, naturalLineValue]
  | k + 1, m, hm => by
      rw [natR, natR_eq (x * x + x * x - 1) k (m / 2) (by rw [pow_succ] at hm; omega)]
      rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
      · have hm2 : m = 2 * (m / 2) := by omega
        rw [h0, Nat.cast_zero, zero_mul, add_zero, one_mul]
        conv_rhs => rw [hm2]
        rw [nlv_even]
      · have hm2 : m = 2 * (m / 2) + 1 := by omega
        rw [h1, Nat.cast_one, one_mul, add_sub_cancel]
        conv_rhs => rw [hm2]
        rw [nlv_odd]

#print axioms df_succ
#print axioms natR_eq

end R1Z.CertBuild

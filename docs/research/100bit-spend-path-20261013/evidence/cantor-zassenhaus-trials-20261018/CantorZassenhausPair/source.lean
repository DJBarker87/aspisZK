import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

noncomputable section
namespace AspisR1.CantorZassenhausPair
variable {K : Type*} [Field K]

/-- The first two random coefficients make evaluations at distinct points
uniform and independent, even after fixing every higher coefficient. -/
def pairEvaluationEquiv (a b ta tb : K) (hab : a ≠ b) : (K × K) ≃ (K × K) where
  toFun c := (c.1 + c.2 * a + ta, c.1 + c.2 * b + tb)
  invFun v := (v.1 - ta - ((v.2 - tb - (v.1 - ta)) / (b-a)) * a,
    (v.2 - tb - (v.1-ta)) / (b-a))
  left_inv c := by
    have h : b-a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    apply Prod.ext <;> dsimp <;> field_simp <;> ring
  right_inv v := by
    have h : b-a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    apply Prod.ext <;> dsimp <;> field_simp <;> ring

variable [Fintype K] [DecidableEq K]
def chi (x : K) : ℚ := (quadraticChar K x : ℤ)
def zeroIndicator (x : K) : ℚ := if x=0 then 1 else 0

theorem chi_sum (hodd : ringChar K ≠ 2) : ∑ x : K, chi x = 0 := by
  simpa [chi] using congrArg (fun z : ℤ => (z : ℚ)) (quadraticChar_sum_zero hodd)

theorem chi_square (x : K) : chi x * chi x = 1 - zeroIndicator x := by
  by_cases hx : x=0
  · simp [chi,zeroIndicator,hx]
  · have h := quadraticChar_sq_one (F := K) hx
    have hc : chi x ^ 2 = 1 := by
      unfold chi
      exact_mod_cast h
    simpa [pow_two,zeroIndicator,hx] using hc

theorem zeroIndicator_sum : ∑ x : K, zeroIndicator x = 1 := by
  simp [zeroIndicator]

theorem chi_square_sum : (∑ x : K, chi x * chi x) = (Fintype.card K : ℚ) - 1 := by
  simp_rw [chi_square]
  rw [Finset.sum_sub_distrib,zeroIndicator_sum]
  simp

def sameCategory (x y : K) : ℚ := if quadraticChar K x=quadraticChar K y then 1 else 0

theorem sameCategory_identity (x y : K) :
    2 * sameCategory x y = (chi x * chi x) * (chi y * chi y) + chi x * chi y +
      2 * zeroIndicator x * zeroIndicator y := by
  by_cases hx : x=0
  · subst x
    by_cases hy : y=0
    · simp [sameCategory,chi,zeroIndicator,hy]
    · have hcy := quadraticChar_eq_zero_iff (F := K) |>.not.mpr hy
      have hcyFun : quadraticCharFun K y ≠ 0 := hcy
      simp [sameCategory,chi,zeroIndicator,hy,Ne.symm hcyFun]
  · by_cases hy : y=0
    · subst y
      have hcx := quadraticChar_eq_zero_iff (F := K) |>.not.mpr hx
      have hcxFun : quadraticCharFun K x ≠ 0 := hcx
      simp [sameCategory,chi,zeroIndicator,hx,hcxFun]
    · simp only [sameCategory,chi,zeroIndicator,if_neg hx,if_neg hy, mul_zero, add_zero]
      rcases quadraticChar_dichotomy (F := K) hx with hpx|hnx <;>
      rcases quadraticChar_dichotomy (F := K) hy with hpy|hny
      all_goals first | rw [hpx,hpy] | rw [hpx,hny] | rw [hnx,hpy] | rw [hnx,hny]
      all_goals norm_num

theorem sameCategory_double_sum (hodd : ringChar K ≠ 2) :
    2 * (∑ x : K, ∑ y : K, sameCategory x y) =
      ((Fintype.card K : ℚ) - 1)^2 + 2 := by
  calc
    _ = ∑ x : K, ∑ y : K, 2 * sameCategory x y := by simp_rw [Finset.mul_sum]
    _ = ∑ x : K, ∑ y : K,
        ((chi x * chi x) * (chi y * chi y) + chi x * chi y +
          2 * zeroIndicator x * zeroIndicator y) := by simp_rw [sameCategory_identity]
    _ = ((∑ x : K, chi x * chi x) * (∑ y : K, chi y * chi y)) +
        (∑ x : K, chi x) * (∑ y : K, chi y) +
        2 * (∑ x : K, zeroIndicator x) * (∑ y : K, zeroIndicator y) := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      rw [← Finset.mul_sum]
    _ = _ := by rw [chi_square_sum,chi_sum hodd,zeroIndicator_sum]; ring

theorem sameCategory_pair_failure_le_half (hodd : ringChar K ≠ 2) :
    (∑ x : K, ∑ y : K, sameCategory x y) /
      ((Fintype.card K : ℚ)^2) ≤ 1/2 := by
  have ho := FiniteField.odd_card_of_char_ne_two hodd
  have hcard : 3 ≤ Fintype.card K := by
    have hn := Fintype.one_lt_card (α := K)
    omega
  have hq : (3 : ℚ) ≤ Fintype.card K := by exact_mod_cast hcard
  have he := sameCategory_double_sum (K := K) hodd
  apply (div_le_iff₀ (sq_pos_of_pos (by linarith : (0 : ℚ)<Fintype.card K))).2
  nlinarith

theorem affine_pair_failure_le_half (a b ta tb : K) (hab : a ≠ b)
    (hodd : ringChar K ≠ 2) :
    (∑ c : K × K, sameCategory (c.1 + c.2*a + ta) (c.1 + c.2*b + tb)) /
      ((Fintype.card K : ℚ)^2) ≤ 1/2 := by
  have hsum : (∑ c : K × K, sameCategory (c.1 + c.2*a + ta) (c.1 + c.2*b + tb)) =
      ∑ v : K × K, sameCategory v.1 v.2 :=
    (pairEvaluationEquiv a b ta tb hab).sum_comp (fun v => sameCategory v.1 v.2)
  rw [hsum,Fintype.sum_prod_type]
  exact sameCategory_pair_failure_le_half hodd

#print axioms affine_pair_failure_le_half
#print axioms sameCategory_double_sum
#print axioms sameCategory_pair_failure_le_half
#print axioms pairEvaluationEquiv
#print axioms chi_sum
#print axioms sameCategory_identity
end AspisR1.CantorZassenhausPair

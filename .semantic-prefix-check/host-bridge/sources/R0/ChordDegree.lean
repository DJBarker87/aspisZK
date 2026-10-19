import Mathlib.Tactic

/-! Symbolic top-coefficient calculation for multiplication by a circle line.
No natural-basis recurrence is normalized at concrete degree 511. -/
set_option autoImplicit false
namespace AspisR0.ChordDegree
open Polynomial
noncomputable section
variable {K : Type*} [Field K]

def mulP0 (a b c : K) (p r : K[X]) : K[X] :=
  C a*p + C b*p*X^1 + C c*r - C c*r*X^2
def mulP1 (a b c : K) (p r : K[X]) : K[X] :=
  C c*p + C a*r + C b*r*X^1

theorem mulP0_coeff (a b c : K) (p r : K[X]) (n : Nat) :
    (mulP0 a b c p r).coeff n = a*p.coeff n +
      (if 1 ≤ n then b*p.coeff (n-1) else 0) + c*r.coeff n -
      (if 2 ≤ n then c*r.coeff (n-2) else 0) := by
  simp only [mulP0, coeff_sub, coeff_add, coeff_mul_X_pow', coeff_C_mul]

theorem mulP1_coeff (a b c : K) (p r : K[X]) (n : Nat) :
    (mulP1 a b c p r).coeff n = c*p.coeff n + a*r.coeff n +
      (if 1 ≤ n then b*r.coeff (n-1) else 0) := by
  simp only [mulP1, coeff_add, coeff_mul_X_pow', coeff_C_mul]

theorem product_degree (a b c : K) (p r : K[X])
    (hp : p.natDegree ≤ 511) (hr : r.natDegree ≤ 511) :
    (mulP0 a b c p r).natDegree ≤ 513 ∧ (mulP1 a b c p r).natDegree ≤ 512 := by
  have pz (n : Nat) (hn : 511 < n) : p.coeff n = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hn)
  have rz (n : Nat) (hn : 511 < n) : r.coeff n = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hr hn)
  constructor
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [mulP0_coeff, if_pos (by omega), if_pos (by omega),
      pz n (by omega), pz (n-1) (by omega), rz n (by omega), rz (n-2) (by omega)]
    ring
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [mulP1_coeff, if_pos (by omega), pz n (by omega),
      rz n (by omega), rz (n-1) (by omega)]
    ring

theorem top_coefficients (a b c : K) (p r : K[X])
    (hp : p.natDegree ≤ 511) (hr : r.natDegree ≤ 511) :
    (mulP0 a b c p r).coeff 513 = -c*r.coeff 511 ∧
    (mulP0 a b c p r).coeff 512 = b*p.coeff 511-c*r.coeff 510 ∧
    (mulP1 a b c p r).coeff 512 = b*r.coeff 511 := by
  have p512 : p.coeff 512 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have p513 : p.coeff 513 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have r512 : r.coeff 512 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have r513 : r.coeff 513 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  simp [mulP0_coeff, mulP1_coeff, p512, p513, r512, r513]

/-- Exactly two conditions, because a genuine line has a nonzero x or y
coefficient. The three possible out-of-range polynomial coefficients are
not three independent image conditions. -/
theorem bounded_product_iff (a b c : K) (p r : K[X])
    (hp : p.natDegree ≤ 511) (hr : r.natDegree ≤ 511) (hbc : b ≠ 0 ∨ c ≠ 0) :
    ((mulP0 a b c p r).natDegree ≤ 511 ∧ (mulP1 a b c p r).natDegree ≤ 511) ↔
      r.coeff 511 = 0 ∧ b*p.coeff 511-c*r.coeff 510 = 0 := by
  obtain ⟨top513, top512, odd512⟩ := top_coefficients a b c p r hp hr
  obtain ⟨deg0, deg1⟩ := product_degree a b c p r hp hr
  constructor
  · rintro ⟨h0, h1⟩
    have hc : c*r.coeff 511 = 0 := by
      have h : (mulP0 a b c p r).coeff 513 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      rw [top513, neg_mul, neg_eq_zero] at h
      exact h
    have hb : b*r.coeff 511 = 0 := by
      rw [← odd512]
      exact coeff_eq_zero_of_natDegree_lt (by omega)
    refine ⟨?_, ?_⟩
    · rcases hbc with h | h
      · exact (mul_eq_zero.mp hb).resolve_left h
      · exact (mul_eq_zero.mp hc).resolve_left h
    · rw [← top512]
      exact coeff_eq_zero_of_natDegree_lt (by omega)
  · rintro ⟨tail, second⟩
    constructor
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro n hn
      by_cases h512 : n = 512
      · simpa only [h512, top512] using second
      by_cases h513 : n = 513
      · simp only [h513, top513, tail, mul_zero]
      exact coeff_eq_zero_of_natDegree_lt (by omega)
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro n hn
      by_cases h512 : n = 512
      · simp only [h512, odd512, tail, mul_zero]
      exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem mul_eval (a b c x y : K) (p r : K[X]) (hcircle : x^2+y^2=1) :
    (mulP0 a b c p r).eval x + y*(mulP1 a b c p r).eval x =
      (a+b*x+c*y)*(p.eval x+y*r.eval x) := by
  simp only [mulP0, mulP1, eval_sub, eval_add, eval_mul, eval_C, eval_X, eval_pow, pow_one]
  linear_combination -(c*r.eval x)*hcircle

#print axioms bounded_product_iff
#print axioms mul_eval
end
end AspisR0.ChordDegree

import AspisV8R17.Mixing

/-! A conditional counting bound for four fixed image residuals.
The source must justify that these residuals are fixed before a fresh
nonzero challenge; this is not itself a Fiat--Shamir bound. -/
set_option autoImplicit false
namespace AspisV8R17
open Polynomial
variable {F : Type*} [Field F]

theorem image_residual_polynomial_ne_zero {n : ℕ} (r : Fin n → F)
    (hbad : ∃ i, r i ≠ 0) : coinPolynomial r ≠ 0 := by
  intro h
  obtain ⟨i,hi⟩ := hbad
  have hc := congrArg (fun p : F[X] => p.coeff i.val) h
  apply hi
  simpa only [coinPolynomial_coeff, coeff_zero] using hc

noncomputable def badImageChallenges [Fintype F] (r : Fin 4 → F) : Finset F := by
  classical
  exact Finset.univ.filter (fun t => t ≠ 0 ∧ t * (coinPolynomial r).eval t = 0)

/-- For a fixed nonzero residual vector there are at most three bad
nonzero challenges, hence at most 3/(|F|-1) under a uniform nonzero draw. -/
theorem badImageChallenges_card [Fintype F] (r : Fin 4 → F)
    (hbad : ∃ i, r i ≠ 0) : (badImageChallenges r).card ≤ 3 := by
  classical
  have hp := image_residual_polynomial_ne_zero r hbad
  apply (Polynomial.card_le_degree_of_subset_roots (p := coinPolynomial r) ?_).trans
    (coinPolynomial_degree r)
  intro t ht
  have ht' : t ≠ 0 ∧ t * (coinPolynomial r).eval t = 0 :=
    (Finset.mem_filter.mp ht).2
  exact (Polynomial.mem_roots hp).mpr ((mul_eq_zero.mp ht'.2).resolve_left ht'.1)

#print axioms image_residual_polynomial_ne_zero
#print axioms badImageChallenges_card

noncomputable def badCombinedChallenges [Fintype F] {n : ℕ}
    (r : Fin (n+1) → F) : Finset F := by
  classical
  exact Finset.univ.filter (fun t => t ≠ 0 ∧ (coinPolynomial r).eval t = 0)

/-- Include the prior ordinary-claim error as the constant coefficient.
Dropping it would incorrectly give the smaller image-only loss for the
whole relation. A two-channel image gate has n=4; 44 query residuals plus
the carried error have n=44. These bounds still require fixed residuals
and a uniform nonzero challenge, not merely the existence of a hash call. -/
theorem badCombinedChallenges_card [Fintype F] {n : ℕ} (r : Fin (n+1) → F)
    (hbad : ∃ i, r i ≠ 0) : (badCombinedChallenges r).card ≤ n := by
  classical
  have hp := image_residual_polynomial_ne_zero r hbad
  apply (Polynomial.card_le_degree_of_subset_roots (p := coinPolynomial r) ?_).trans
    (coinPolynomial_degree r)
  intro t ht
  have ht' : t ≠ 0 ∧ (coinPolynomial r).eval t = 0 :=
    (Finset.mem_filter.mp ht).2
  exact (Polynomial.mem_roots hp).mpr ht'.2

#print axioms badCombinedChallenges_card
end AspisV8R17

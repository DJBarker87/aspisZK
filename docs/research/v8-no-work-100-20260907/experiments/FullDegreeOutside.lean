import AspisFormal.V5FriConcreteEncoderApplicability

/-! A new obstruction, not another fixed-target probability lemma.
The ambient Laurent word T_512(x) lies outside the selected circle space.
After multiplying by z^512, its two endpoint coefficients sum to one;
every selected message has endpoint sum zero. Root counting then bounds
agreement by 1024, irrespective of which message an adaptive prover selects.
The generic theorem keeps the circle-encoder and distinct-z bridges explicit.
No concrete field enumeration or giant polynomial-power normalization. -/

set_option autoImplicit false
namespace AspisV8.FullDegreeOutside
open Polynomial Finset
variable {K : Type*} [Field K]

noncomputable def ambientWordPolynomial (a : K) (n : ℕ) : K[X] :=
  C a + C a * X^n

theorem ambient_endpoint_sum (a : K) (n : ℕ) (hn : 0 < n) :
    (ambientWordPolynomial a n).coeff 0 + (ambientWordPolynomial a n).coeff n = a+a := by
  simp [ambientWordPolynomial, Polynomial.coeff_C, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Nat.ne_of_gt hn, Nat.ne_of_lt hn]

theorem ambient_degree_le (a : K) (n : ℕ) :
    (ambientWordPolynomial a n).natDegree ≤ n := by
  apply (Polynomial.natDegree_add_le _ _).trans
  exact max_le (by simp) (Polynomial.natDegree_C_mul_X_pow_le a n)

/-- No original code polynomial, even one chosen after all earlier challenges,
can equal this fixed ambient word. -/
theorem outside_every_constrained_polynomial (a : K) (n : ℕ) (hn : 0 < n)
    (ha : a+a ≠ 0) (g : K[X]) (hconstraint : g.coeff 0 + g.coeff n = 0) :
    ambientWordPolynomial a n - g ≠ 0 := by
  intro hz
  have heq := sub_eq_zero.mp hz
  have h := ambient_endpoint_sum a n hn
  rw [heq, hconstraint] at h
  exact ha h.symm

/-- Universal quantitative agreement cap, not a success-conditional decoder
claim. S may contain every distinct z in the actual evaluation domain. -/
theorem adaptive_original_agreement_cap [DecidableEq K]
    (S : Finset K) (a : K) (n : ℕ) (hn : 0 < n) (ha : a+a ≠ 0)
    (g : K[X]) (hg : g.natDegree ≤ n) (hconstraint : g.coeff 0 + g.coeff n = 0) :
    (S.filter fun z => (ambientWordPolynomial a n).eval z = g.eval z).card ≤ n := by
  have hne := outside_every_constrained_polynomial a n hn ha g hconstraint
  have hdeg : (ambientWordPolynomial a n-g).natDegree ≤ n :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le (ambient_degree_le a n) hg)
  apply (Polynomial.card_le_degree_of_subset_roots (p := ambientWordPolynomial a n-g) ?_).trans hdeg
  intro z hz
  apply (Polynomial.mem_roots hne).mpr
  change (ambientWordPolynomial a n-g).eval z = 0
  rw [Polynomial.eval_sub, (Finset.mem_filter.mp hz).2, sub_self]

theorem no_initial_decoder_candidate [DecidableEq K]
    (S : Finset K) (a : K) (ha : a+a ≠ 0) (g : K[X])
    (hg : g.natDegree ≤ 1024) (hconstraint : g.coeff 0 + g.coeff 1024 = 0) :
    ¬ 38230 ≤ (S.filter fun z => (ambientWordPolynomial a 1024).eval z = g.eval z).card := by
  have h := adaptive_original_agreement_cap S a 1024 (by decide) ha g hg hconstraint
  omega

#print axioms ambient_endpoint_sum
#print axioms outside_every_constrained_polynomial
#print axioms adaptive_original_agreement_cap
#print axioms no_initial_decoder_candidate
end AspisV8.FullDegreeOutside

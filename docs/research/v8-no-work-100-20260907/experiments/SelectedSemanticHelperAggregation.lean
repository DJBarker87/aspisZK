import JointImageGame

/-! Exact selected mu/mu^2 Boolean-table aggregation, not the older
linear-helper V7 terminal. All tables/coefficients precede mu. They may depend
on earlier lambda, chi, theta and equality-point challenges; later rewards
remain arbitrary functions of mu. Authentication and the ten-round bridge
are not assumptions disguised as row correctness.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.SelectedSemanticHelperAggregation
open Polynomial Finset
open AspisV5FriConcreteEncoderApplicability AspisV8.JointImageGame
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K]

def aggregatePolynomial (constraint helper inactive : K) : K[X] :=
  monomialPolynomial ![constraint, helper, inactive]

theorem aggregate_eval (constraint helper inactive mu : K) :
    (aggregatePolynomial constraint helper inactive).eval mu =
      constraint+mu*helper+mu^2*inactive := by
  simp [aggregatePolynomial, monomialPolynomial, Fin.sum_univ_succ]
  ring

theorem aggregate_degree (constraint helper inactive : K) :
    (aggregatePolynomial constraint helper inactive).natDegree ≤ 2 :=
  monomialPolynomial_natDegree_le (by decide : 0 < 3) _

theorem aggregate_zero_iff (constraint helper inactive : K) :
    aggregatePolynomial constraint helper inactive=0 ↔
      constraint=0 ∧ helper=0 ∧ inactive=0 := by
  constructor
  · intro zero
    have coefficients (i : Fin 3) : (![constraint, helper, inactive] : Fin 3 → K) i=0 := by
      have equal := congrArg (fun p : K[X] => p.coeff i.val) zero
      simpa only [aggregatePolynomial, monomialPolynomial_coeff, Polynomial.coeff_zero] using equal
    exact ⟨coefficients 0, coefficients 1, coefficients 2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simp [aggregatePolynomial, monomialPolynomial]

/-- Boolean restriction of pair_forest_semantic_terminal::terminal_parts.
Weights are the source equality weights and active is its fixed copy mask.
The generic index type permits the actual1024 rows without enumerating them. -/
def unmaskedTable {I : Type*} (weight composition helper active : I → K)
    (mu : K) (row : I) : K :=
  weight row*composition row+mu*helper row+mu^2*((1-active row)*helper row)

theorem source_sum {I : Type*} (R : Finset I)
    (weight composition helper active : I → K) (mu : K) :
    (∑ row ∈ R, unmaskedTable weight composition helper active mu row) =
      (aggregatePolynomial (∑ row ∈ R, weight row*composition row)
        (∑ row ∈ R, helper row) (∑ row ∈ R, (1-active row)*helper row)).eval mu := by
  rw [aggregate_eval]
  simp only [unmaskedTable, Finset.sum_add_distrib, Finset.mul_sum]

/-- Empty on the identically zero branch. Otherwise these are exactly the
roots within the original mu domain, with no resampling or renormalization. -/
def badMu (S : Finset K) (constraint helper inactive : K) : Finset K :=
  if aggregatePolynomial constraint helper inactive=0 then ∅
  else S.filter fun mu => (aggregatePolynomial constraint helper inactive).eval mu=0

theorem badMu_card (S : Finset K) (constraint helper inactive : K) :
    (badMu S constraint helper inactive).card ≤ 2 := by
  classical
  by_cases zero : aggregatePolynomial constraint helper inactive=0
  · simp only [badMu, if_pos zero, Finset.card_empty]
    omega
  · rw [badMu, if_neg zero]
    exact root_count S _ zero 2 (aggregate_degree constraint helper inactive)

theorem aggregate_zero_or_collision (S : Finset K) (constraint helper inactive mu : K)
    (inside : mu ∈ S) (zero : constraint+mu*helper+mu^2*inactive=0) :
    (constraint=0 ∧ helper=0 ∧ inactive=0) ∨ mu ∈ badMu S constraint helper inactive := by
  classical
  by_cases identical : aggregatePolynomial constraint helper inactive=0
  · exact Or.inl ((aggregate_zero_iff constraint helper inactive).mp identical)
  · apply Or.inr
    rw [badMu, if_neg identical]
    exact Finset.mem_filter.mpr ⟨inside, (aggregate_eval constraint helper inactive mu).trans zero⟩

/-- Total deterministic source-shaped alternative: zero aggregate alone
does not imply its three coefficients vanish at a colliding mu. -/
theorem source_zero_or_collision {I : Type*} (R : Finset I)
    (weight composition helper active : I → K) (S : Finset K) (mu : K)
    (inside : mu ∈ S)
    (accepted : (∑ row ∈ R, unmaskedTable weight composition helper active mu row)=0) :
    ((∑ row ∈ R, weight row*composition row)=0 ∧
      (∑ row ∈ R, helper row)=0 ∧ (∑ row ∈ R, (1-active row)*helper row)=0) ∨
    mu ∈ badMu S (∑ row ∈ R, weight row*composition row)
      (∑ row ∈ R, helper row) (∑ row ∈ R, (1-active row)*helper row) := by
  apply aggregate_zero_or_collision S _ _ _ mu inside
  rw [source_sum, aggregate_eval] at accepted
  exact accepted

/-- A continuation may depend on mu and all later challenges. Only the
three coefficients must be fixed before the displayed uniform mu average.
This is an ideal finite-mean bound, not a Fiat--Shamir freshness theorem. -/
theorem collision_continuation_bound (S : Finset K) (nonempty : S.Nonempty)
    (constraint helper inactive : K) (reward : K → ℚ)
    (unit : ∀ mu ∈ S, reward mu ≤ 1) :
    avg S (fun mu => if ¬(constraint=0 ∧ helper=0 ∧ inactive=0) ∧
      constraint+mu*helper+mu^2*inactive=0 then reward mu else 0) ≤ (2 : ℚ)/S.card := by
  classical
  by_cases allZero : constraint=0 ∧ helper=0 ∧ inactive=0
  · simp only [allZero, not_true_eq_false, false_and, if_false, avg,
      Finset.sum_const_zero, zero_div]
    positivity
  · have polynomialNonzero : aggregatePolynomial constraint helper inactive ≠ 0 :=
      fun zero => allZero ((aggregate_zero_iff constraint helper inactive).mp zero)
    have bound := avg_polynomial S nonempty (aggregatePolynomial constraint helper inactive)
      polynomialNonzero 2 (aggregate_degree constraint helper inactive)
      (fun mu => if ¬(constraint=0 ∧ helper=0 ∧ inactive=0) ∧
        constraint+mu*helper+mu^2*inactive=0 then reward mu else 0)
      0 (by norm_num)
      (by
        intro mu member
        split_ifs
        · exact unit mu member
        · norm_num)
      (by
        intro mu member nonroot
        have notZero : constraint+mu*helper+mu^2*inactive ≠ 0 := by
          rw [← aggregate_eval]
          exact nonroot
        simp only [notZero, and_false, if_false, le_refl])
    simpa only [add_zero] using bound

/-- Sharp two-root regression, realizable by one active and one inactive
helper value. This does not assert local copy-row acceptance. -/
theorem quadratic_regression (mu : K) :
    (∑ row : Fin 2, unmaskedTable (fun _ => 1) ![1,0] ![1,-1] ![1,0] mu row) =
      1-mu^2 := by
  simp [unmaskedTable, Fin.sum_univ_succ]
  ring

theorem regression_two_roots (two : (2 : K) ≠ 0) :
    aggregatePolynomial (1 : K) 0 (-1) ≠ 0 ∧
    (aggregatePolynomial (1 : K) 0 (-1)).eval 1=0 ∧
    (aggregatePolynomial (1 : K) 0 (-1)).eval (-1)=0 ∧ (1 : K) ≠ -1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro zero
    exact one_ne_zero ((aggregate_zero_iff (1 : K) 0 (-1)).mp zero).1
  · rw [aggregate_eval]
    ring
  · rw [aggregate_eval]
    ring
  · intro equal
    apply two
    calc
      (2 : K)=1+1 := by ring
      _ = -1+1 := congrArg (fun value : K => value+1) equal
      _ = 0 := by ring

#print axioms aggregate_eval
#print axioms aggregate_zero_iff
#print axioms source_sum
#print axioms badMu_card
#print axioms source_zero_or_collision
#print axioms collision_continuation_bound
#print axioms quadratic_regression
#print axioms regression_two_roots
end
end AspisV8.SelectedSemanticHelperAggregation

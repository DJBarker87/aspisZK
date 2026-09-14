import Mathlib

/-!
# Acceptance-weighted restoration: rejection is not a negligible event

These finite real-weight lemmas explain precisely what can be obtained from
retries and from two independent suffixes sharing one PRE-ANSWER prefix.
They must not be applied to a prefix selected retrospectively from a finished
accepting execution without a separate law/disintegration proof.

The source root sweep is NOT changed to perform retries by this file.
-/
set_option autoImplicit false
namespace AspisK1.V7Tag73AcceptanceWeightedRestoration
open scoped BigOperators
noncomputable section
variable {H : Type*} [Fintype H]

def mean (w p : H → ℝ) : ℝ := ∑ h, w h * p h

def secondMoment (w p : H → ℝ) : ℝ := ∑ h, w h * (p h)^2

/-- Finite weighted variance identity with unit total prefix mass. -/
theorem variance_identity (w p : H → ℝ) (total : ∑ h, w h = 1) :
    (∑ h, w h * (p h - mean w p)^2) =
      secondMoment w p - (mean w p)^2 := by
  let m := mean w p
  calc
    (∑ h, w h * (p h - mean w p)^2) =
        ∑ h, (w h * (p h)^2 - (2*m) * (w h*p h) + m^2*w h) := by
      apply Finset.sum_congr rfl
      intro h _
      change w h * (p h - m)^2 = _
      ring
    _ = secondMoment w p - (2*m) * mean w p + m^2 * (∑ h, w h) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum, mean, secondMoment]
    _ = secondMoment w p - (mean w p)^2 := by rw [total]; dsimp [m]; ring

/-- Shared-prefix successful-rerun mass naturally introduces a square.
This is not the stronger linear extraction claim. -/
theorem mean_sq_le_secondMoment (w p : H → ℝ)
    (nonnegative : ∀ h, 0 ≤ w h) (total : ∑ h, w h = 1) :
    (mean w p)^2 ≤ secondMoment w p := by
  have nonneg : 0 ≤ ∑ h, w h * (p h - mean w p)^2 :=
    Finset.sum_nonneg fun h _ => mul_nonneg (nonnegative h) (sq_nonneg _)
  rw [variance_identity w p total] at nonneg
  linarith

/-- At each pre-answer prefix, accepted mass is at most good plus bad mass.
The overlap need not be disjoint for this lower bound. -/
theorem two_run_good_lower_bound
    (w p good bad : H → ℝ) (epsilon : ℝ)
    (weightNonnegative : ∀ h, 0 ≤ w h) (total : ∑ h, w h = 1)
    (acceptNonnegative : ∀ h, 0 ≤ p h)
    (cover : ∀ h, p h ≤ good h + bad h)
    (badBound : ∀ h, bad h ≤ epsilon) :
    (mean w p)^2 ≤ (∑ h, w h * p h * good h) + epsilon * mean w p := by
  apply (mean_sq_le_secondMoment w p weightNonnegative total).trans
  calc
    secondMoment w p ≤ ∑ h, (w h * p h * good h + epsilon * (w h*p h)) := by
      apply Finset.sum_le_sum
      intro h _
      have h1 := mul_le_mul_of_nonneg_left (cover h) (acceptNonnegative h)
      have h2 := mul_le_mul_of_nonneg_left (badBound h) (acceptNonnegative h)
      have h3 : (p h)^2 ≤ p h*good h + epsilon*p h := by nlinarith
      have h4 := mul_le_mul_of_nonneg_left h3 (weightNonnegative h)
      nlinarith
    _ = (∑ h, w h*p h*good h) + epsilon*mean w p := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum, mean]

/-- Division-free geometric conservation for rejection q = 1-p. -/
theorem geometric_acceptance_partition (p q : ℝ)
    (partition : p + q = 1) (n : Nat) :
    p * (∑ i ∈ Finset.range n, q^i) + q^n = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      nlinarith

private theorem unit_power_antitone (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (m n : Nat) (le : m ≤ n) : q^n ≤ q^m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le le
  rw [pow_add]
  have hk : q^k ≤ 1 := pow_le_one₀ hq hq1
  simpa using mul_le_mul_of_nonneg_left hk (pow_nonneg hq m)

/-- A uniform additive failure bound cannot be obtained by declaring one
rejecting restoration negligible. Even r retries generally leave this term. -/
theorem acceptance_weighted_all_reject_bound (p : ℝ)
    (p0 : 0 ≤ p) (p1 : p ≤ 1) (r : Nat) :
    p * (1-p)^r ≤ 1 / ((r+1 : Nat) : ℝ) := by
  let q := 1-p
  have q0 : 0 ≤ q := by dsimp [q]; linarith
  have q1 : q ≤ 1 := by dsimp [q]; linarith
  have every : ∀ i ∈ Finset.range (r+1), q^r ≤ q^i := by
    intro i hi
    exact unit_power_antitone q q0 q1 i r (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  have lower : ((r+1 : Nat) : ℝ) * q^r ≤ ∑ i ∈ Finset.range (r+1), q^i := by
    calc
      ((r+1 : Nat) : ℝ) * q^r = ∑ _i ∈ Finset.range (r+1), q^r := by simp
      _ ≤ _ := Finset.sum_le_sum every
  have balance := geometric_acceptance_partition p q (by dsimp [q]; ring) (r+1)
  have tail0 := pow_nonneg q0 (r+1)
  have scaled := mul_le_mul_of_nonneg_left lower p0
  have denominator : (0 : ℝ) < ((r+1 : Nat) : ℝ) := by positivity
  apply (le_div_iff₀ denominator).mpr
  change p*q^r*((r+1 : Nat) : ℝ) ≤ 1
  nlinarith

/-- A concrete negative control: one replay at acceptance probability 1/2
leaves joint original-accept/rerun-reject mass 1/4, not a tiny field-root error. -/
theorem one_replay_quarter_failure : (1/2 : ℝ) * (1-1/2)^1 = 1/4 := by norm_num

/-- Jensen cannot upgrade a successful-pair square to a linear claim. -/
theorem square_not_linear : ¬ ((1/2 : ℝ) ≤ (1/2)^2) := by norm_num

#print axioms variance_identity
#print axioms mean_sq_le_secondMoment
#print axioms two_run_good_lower_bound
#print axioms geometric_acceptance_partition
#print axioms acceptance_weighted_all_reject_bound
#print axioms one_replay_quarter_failure
end
end AspisK1.V7Tag73AcceptanceWeightedRestoration

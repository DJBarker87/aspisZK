import Mathlib

/-!
Exact rational identities for the complete bounded rejection decoder.

They state the per-value and success masses on an IID uniform word tape.  No
actual-source freshness, cache, restoration, or probability transport premise
is introduced here.
-/
namespace AspisV8Completion.FSV8ExactRejectionWeights

def geom (r : ℚ) (k : Nat) : ℚ := ∑ j ∈ Finset.range k, r ^ j

lemma geom_identity (r : ℚ) (k : Nat) :
    (1 - r) * geom r k = 1 - r ^ k := by
  induction k with
  | zero => simp [geom]
  | succ k ih =>
      have step : geom r (k + 1) = geom r k + r ^ k := by
        simp [geom, Finset.sum_range_succ]
      rw [step, mul_add, ih, pow_succ]
      ring

/-- Mass of one fixed canonical limb value for a cap-`k` rejection sampler
over `n` equiprobable words with one sentinel. -/
def perValueWeight (n : ℚ) (k : Nat) : ℚ := n⁻¹ * geom n⁻¹ k

theorem perValueWeight_partition (n : ℚ) (hn : n ≠ 0) (k : Nat) :
    (n - 1) * perValueWeight n k = 1 - (n⁻¹) ^ k := by
  have hcoeff : (n - 1) * n⁻¹ = 1 - n⁻¹ := by
    rw [sub_mul, mul_inv_cancel₀ hn, one_mul]
  unfold perValueWeight
  rw [← mul_assoc, hcoeff, geom_identity]

theorem perValueWeight_closed_form (n : ℚ) (hn : n ≠ 0)
    (hn1 : n - 1 ≠ 0) (k : Nat) :
    perValueWeight n k = (1 - (n⁻¹) ^ k) / (n - 1) := by
  apply (eq_div_iff hn1).2
  rw [mul_comm]
  exact perValueWeight_partition n hn k

/-- Exact four-limb partition.  Thus every fixed four-limb tuple has mass
`perValueWeight n k ^ 4`, while total success has mass
`(1 - (n⁻¹)^k)^4`. -/
theorem four_limb_mass_partition (n : ℚ) (hn : n ≠ 0) (k : Nat) :
    (n - 1) ^ 4 * (perValueWeight n k) ^ 4 =
      (1 - (n⁻¹) ^ k) ^ 4 := by
  rw [← mul_pow, perValueWeight_partition n hn]

/-- Point mass of any fixed returned tuple equals total decoder-success mass
divided by the number `(n-1)^4` of canonical tuples. -/
theorem fixedTupleWeight_eq_success_div (n : ℚ) (hn : n ≠ 0)
    (hn1 : n - 1 ≠ 0) (k : Nat) :
    (perValueWeight n k) ^ 4 =
      (1 - (n⁻¹) ^ k) ^ 4 / (n - 1) ^ 4 := by
  apply (eq_div_iff (pow_ne_zero 4 hn1)).2
  rw [mul_comm]
  exact four_limb_mass_partition n hn k

/-- Exact V8 ordinary-challenge instance: `n=2^31`, cap 8. -/
theorem v8_four_limb_mass_partition :
    (((2 : ℚ) ^ 31) - 1) ^ 4 *
        (perValueWeight ((2 : ℚ) ^ 31) 8) ^ 4 =
      (1 - ((((2 : ℚ) ^ 31)⁻¹) ^ 8)) ^ 4 := by
  exact four_limb_mass_partition ((2 : ℚ) ^ 31) (by positivity) 8

/-- Normalized bounded-geometric wait law. -/
theorem normalized_wait_sum (r : ℚ) (k : Nat) (h : geom r k ≠ 0) :
    (∑ j ∈ Finset.range k, r ^ j / geom r k) = 1 := by
  rw [← Finset.sum_div]
  change geom r k / geom r k = 1
  exact div_self h

#print axioms geom_identity
#print axioms perValueWeight_partition
#print axioms perValueWeight_closed_form
#print axioms four_limb_mass_partition
#print axioms fixedTupleWeight_eq_success_div
#print axioms v8_four_limb_mass_partition
#print axioms normalized_wait_sum
end AspisV8Completion.FSV8ExactRejectionWeights

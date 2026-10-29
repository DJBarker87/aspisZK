import PV_MEAS_Average

/-! Explicit uniform measure for finite carriers; no computation of the carrier. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace PV_MEAS_Uniform

variable (M : Type*) [Fintype M] [Nonempty M] [MeasurableSpace M]
  [MeasurableSingletonClass M]

def uniformMeasure : Measure M :=
  (Fintype.card M : ℝ≥0∞)⁻¹ • ∑ m : M, Measure.dirac m

instance uniform_probability : IsProbabilityMeasure (uniformMeasure M) := by
  constructor
  simp [uniformMeasure, Measure.smul_apply, Measure.sum_apply,
    Fintype.card_ne_zero, ENNReal.natCast_ne_top]

def uniform : ProbabilityMeasure M := ⟨uniformMeasure M, inferInstance⟩

theorem integral_uniform (f : M → ℝ) :
    (∫ m, f m ∂(uniform M : Measure M)) =
      (∑ m : M, f m) / (Fintype.card M : ℝ) := by
  change (∫ m, f m ∂uniformMeasure M) = _
  rw [uniformMeasure, integral_smul_measure, integral_finsetSum_measure]
  · simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      smul_eq_mul, div_eq_mul_inv, mul_comm]
  · intro m _
    exact integrable_dirac (by simp)

/-- Fubini for finite uniform laws, by sums rather than carrier reduction. -/
theorem integral_uniform_product {C R : Type*} [Fintype C] [Nonempty C]
    [Fintype R] [Nonempty R] [MeasurableSpace C] [MeasurableSingletonClass C]
    [MeasurableSpace R] [MeasurableSingletonClass R] (f : C × R → ℝ) :
    (∫ p, f p ∂(uniform (C × R) : Measure (C × R))) =
      ∫ c, (∫ r, f (c,r) ∂(uniform R : Measure R)) ∂(uniform C : Measure C) := by
  simp only [integral_uniform, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type]
  rw [← Finset.sum_div]
  ring

#print axioms integral_uniform_product
#print axioms uniform_probability
#print axioms integral_uniform
end PV_MEAS_Uniform

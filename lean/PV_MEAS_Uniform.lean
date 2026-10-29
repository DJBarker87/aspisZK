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
  simp [uniformMeasure, Measure.smul_apply, Measure.finsetSum_apply,
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

/-- Projection of the finite uniform joint law has the finite uniform marginal. -/
theorem uniform_fst (C R : Type*) [Fintype C] [Nonempty C] [Fintype R] [Nonempty R]
    [MeasurableSpace C] [MeasurableSingletonClass C]
    [MeasurableSpace R] [MeasurableSingletonClass R] :
    Measure.map Prod.fst (uniform (C × R) : Measure (C × R)) =
      Measure.map id (uniform C : Measure C) := by
  classical
  rw [Measure.map_id]
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply measurable_fst hs]
  simp only [uniform, uniformMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.finsetSum_apply,
    Measure.dirac_apply, Set.indicator_apply, Pi.one_apply, Set.mem_preimage,
    Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  rw [ENNReal.mul_inv]
  have hr : (Fintype.card R : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ = (Fintype.card C : ℝ≥0∞)⁻¹ *
        (((Fintype.card R : ℝ≥0∞)⁻¹ * Fintype.card R) *
          ∑ c : C, if c ∈ s then (1 : ℝ≥0∞) else 0) := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hr ENNReal.natCast_ne_top, one_mul]

#print axioms uniform_fst
#print axioms integral_uniform_product
#print axioms uniform_probability
#print axioms integral_uniform
end PV_MEAS_Uniform

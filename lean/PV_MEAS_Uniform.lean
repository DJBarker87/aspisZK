import PV_MEAS_Average
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! Explicit uniform measure for finite carriers; no computation of the carrier. -/
set_option autoImplicit false
noncomputable section
open scoped ENNReal
open MeasureTheory PV_MEAS_Law
namespace PV_MEAS_Uniform

variable (M : Type*) [Fintype M] [Nonempty M] [MeasurableSpace M]
  [MeasurableSingletonClass M]

def uniformMeasure : Measure M :=
  (Fintype.card M : ℝ≥0∞)⁻¹ • ∑ m : M, Measure.dirac m

instance uniform_probability : IsProbabilityMeasure (uniformMeasure M) := by
  constructor
  simp only [uniformMeasure, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply,
    measure_univ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast (Fintype.card_ne_zero (α := M))) (ENNReal.natCast_ne_top (Fintype.card M))

def uniform : ProbabilityMeasure M := ⟨uniformMeasure M, inferInstance⟩

theorem integral_uniform (f : M → ℝ) (nonneg : ∀ m, 0 ≤ f m) :
    (∫ₚ m, f m ∂(uniform M : Measure M)) =
      (∑ m : M, f m) / (Fintype.card M : ℝ) := by
  change (∫⁻ m, ENNReal.ofReal (f m) ∂uniformMeasure M).toReal = _
  rw [uniformMeasure, lintegral_smul_measure, lintegral_finsetSum_measure]
  simp only [lintegral_dirac, smul_eq_mul]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum (by intro m _; exact ENNReal.ofReal_ne_top)]
  simp only [ENNReal.toReal_ofReal (nonneg _), div_eq_mul_inv, mul_comm]

/-- Fubini for finite uniform laws, by sums rather than carrier reduction. -/
theorem integral_uniform_product {C R : Type*} [Fintype C] [Nonempty C]
    [Fintype R] [Nonempty R] [MeasurableSpace C] [MeasurableSingletonClass C]
    [MeasurableSpace R] [MeasurableSingletonClass R] (f : C × R → ℝ)
    (nonneg : ∀ p, 0 ≤ f p) :
    (∫ₚ p, f p ∂(uniform (C × R) : Measure (C × R))) =
      ∫ₚ c, (∫ₚ r, f (c,r) ∂(uniform R : Measure R)) ∂(uniform C : Measure C) := by
  rw [integral_uniform (C × R) f nonneg,
    integral_uniform C (fun c => ∫ₚ r, f (c,r) ∂(uniform R : Measure R))
      (fun _ => ENNReal.toReal_nonneg)]
  have inner (c : C) : (∫ₚ r, f (c,r) ∂(uniform R : Measure R)) =
      (∑ r : R, f (c,r)) / (Fintype.card R : ℝ) :=
    integral_uniform R _ (fun r => nonneg (c,r))
  simp_rw [inner]
  simp only [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type]
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
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top (Fintype.card R))) (Or.inl (ENNReal.natCast_ne_top (Fintype.card C)))]
  have hr : (Fintype.card R : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero (α := R))
  calc
    _ = (Fintype.card C : ℝ≥0∞)⁻¹ *
        (((Fintype.card R : ℝ≥0∞)⁻¹ * Fintype.card R) *
          ∑ c : C, if c ∈ s then (1 : ℝ≥0∞) else 0) := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hr (ENNReal.natCast_ne_top (Fintype.card R)), one_mul]

#print axioms uniform_fst
#print axioms integral_uniform_product
#print axioms uniform_probability
#print axioms integral_uniform
end PV_MEAS_Uniform

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! General probability-law averaging. Preregistered statement: see
 evidence/pv-meas-20261029/DESIGN.md and authority-gap receipt.
 No finite support, uniformity or rational mass hypothesis. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace PV_MEAS_Average

/-- Pointwise privacy survives arbitrary probability mixtures. Integrability
is explicit here; bounded measurable decision probabilities imply it. -/
theorem average_bound {E : Type*} [MeasurableSpace E]
    (μ : ProbabilityMeasure E) (p q : E → ℝ) (eps : ℝ)
    (hp : Integrable p (μ : Measure E))
    (hq : Integrable q (μ : Measure E))
    (per_env : ∀ e, |p e - q e| ≤ eps) :
    |(∫ e, p e ∂(μ : Measure E)) - ∫ e, q e ∂(μ : Measure E)| ≤ eps := by
  rw [← integral_sub hp hq]
  have h := norm_integral_le_of_norm_le_const
    (μ := (μ : Measure E)) (f := fun e => p e - q e)
    (ae_of_all _ (fun e => (Real.norm_eq_abs _).trans_le (per_env e)))
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h

/-- Equal laws transport expectations on arbitrary measurable spaces.
This is exact pushforward transport, with no independence assumption. -/
theorem expectation_eq_of_equal_laws
    {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) (f : X → Z) (g : Y → Z)
    (hf : Measurable f) (hg : Measurable g)
    (law : Measure.map f μ = Measure.map g ν)
    (test : Z → ℝ) (htest : Measurable test) :
    (∫ x, test (f x) ∂μ) = ∫ y, test (g y) ∂ν := by
  rw [← integral_map hf.aemeasurable htest.aestronglyMeasurable,
    law, integral_map hg.aemeasurable htest.aestronglyMeasurable]

/-- Measurable decision probabilities are integrable without any finite-carrier
or bounded-timing assumption. Only the decision probability lies in [0,1]. -/
theorem decision_integrable {E : Type*} [MeasurableSpace E]
    (μ : ProbabilityMeasure E) (p : E → ℝ) (hp : Measurable p)
    (bounded : ∀ e, 0 ≤ p e ∧ p e ≤ 1) : Integrable p (μ : Measure E) := by
  exact integrable_of_le_of_le hp.aestronglyMeasurable
    (ae_of_all _ (fun e => (bounded e).1))
    (ae_of_all _ (fun e => (bounded e).2)) (integrable_const 0) (integrable_const 1)

#print axioms decision_integrable
#print axioms average_bound
#print axioms expectation_eq_of_equal_laws
end PV_MEAS_Average

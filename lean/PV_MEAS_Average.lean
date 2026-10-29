import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Dirac

/-! Probability expectations, using nonnegative Lebesgue integration.
The bundled law below is the underlying subtype used by Mathlib's
ProbabilityMeasure, without importing its topological API. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace PV_MEAS_Law
abbrev ProbabilityMeasure (E : Type*) [MeasurableSpace E] :=
  { μ : Measure E // IsProbabilityMeasure μ }
instance probability {E : Type*} [MeasurableSpace E] (μ : ProbabilityMeasure E) :
    IsProbabilityMeasure (μ : Measure E) := μ.2
 theorem ProbabilityMeasure.nonempty {E : Type*} [MeasurableSpace E]
    (μ : ProbabilityMeasure E) : Nonempty E := nonempty_of_isProbabilityMeasure (μ : Measure E)
def expectation {E : Type*} [MeasurableSpace E] (μ : Measure E) (p : E → ℝ) : ℝ :=
  (∫⁻ e, ENNReal.ofReal (p e) ∂μ).toReal
notation3 "∫ₚ " (...) ", " r:60 " ∂" μ:70 => expectation μ (fun ... => r)
#print axioms ProbabilityMeasure.nonempty
end PV_MEAS_Law

open PV_MEAS_Law
namespace PV_MEAS_Average

theorem finite_of_bound {E : Type*} [MeasurableSpace E]
    (μ : ProbabilityMeasure E) (p : E → ℝ) (C : ℝ) (bound : ∀ e, p e ≤ C) :
    (∫⁻ e, ENNReal.ofReal (p e) ∂(μ : Measure E)) ≠ ∞ := by
  have h := lintegral_mono (fun e => ENNReal.ofReal_le_ofReal (bound e)) (μ := (μ : Measure E))
  exact ne_top_of_le_ne_top (by simp only [lintegral_const, measure_univ, mul_one, ENNReal.ofReal_ne_top]) h

theorem decision_integrable {E : Type*} [MeasurableSpace E]
    (μ : ProbabilityMeasure E) (p : E → ℝ) (_hp : Measurable p)
    (bounded : ∀ e, 0 ≤ p e ∧ p e ≤ 1) :
    (∫⁻ e, ENNReal.ofReal (p e) ∂(μ : Measure E)) ≠ ∞ :=
  finite_of_bound μ p 1 (fun e => (bounded e).2)

theorem decision_probability_bounds {E : Type*} [MeasurableSpace E]
    (μ : ProbabilityMeasure E) (p : E → ℝ) (_hp : Measurable p)
    (bounded : ∀ e, 0 ≤ p e ∧ p e ≤ 1) :
    0 ≤ (∫ₚ e, p e ∂(μ : Measure E)) ∧ (∫ₚ e, p e ∂(μ : Measure E)) ≤ 1 := by
  constructor
  · exact ENNReal.toReal_nonneg
  · have h := lintegral_mono (fun e => ENNReal.ofReal_le_ofReal (bounded e).2) (μ := (μ : Measure E))
    simpa only [expectation, lintegral_const, measure_univ, mul_one, ENNReal.ofReal_one,
      ENNReal.toReal_one] using ENNReal.toReal_mono (by simp) h

theorem expectation_const {E : Type*} [MeasurableSpace E]
    (μ : ProbabilityMeasure E) (c : ℝ) (hc : 0 ≤ c) :
    (∫ₚ _ : E, c ∂(μ : Measure E)) = c := by
  simp only [expectation, lintegral_const, measure_univ, mul_one, ENNReal.toReal_ofReal hc]

/-- A pointwise nonnegative additive majorant transports to expectations. -/
theorem expectation_le_add {E : Type*} [MeasurableSpace E]
    (μ : ProbabilityMeasure E) (p q b : E → ℝ) (hq : Measurable q)
    (q_nonneg : ∀ e, 0 ≤ q e) (b_nonneg : ∀ e, 0 ≤ b e)
    (Cq Cb : ℝ) (q_bound : ∀ e, q e ≤ Cq) (b_bound : ∀ e, b e ≤ Cb)
    (control : ∀ e, p e ≤ q e + b e) :
    (∫ₚ e, p e ∂(μ : Measure E)) ≤
      (∫ₚ e, q e ∂(μ : Measure E)) + ∫ₚ e, b e ∂(μ : Measure E) := by
  have h := lintegral_mono (fun e => ENNReal.ofReal_le_ofReal (control e)) (μ := (μ : Measure E))
  simp_rw [ENNReal.ofReal_add (q_nonneg _) (b_nonneg _)] at h
  rw [lintegral_add_left hq.ennreal_ofReal] at h
  have hqf := finite_of_bound μ q Cq q_bound
  have hbf := finite_of_bound μ b Cb b_bound
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hqf,hbf⟩) h
  rw [ENNReal.toReal_add hqf hbf] at hr
  exact hr

/-- Arbitrary probability mixtures of measurable decision probabilities. -/
theorem average_bound {E : Type*} [MeasurableSpace E]
    (μ : ProbabilityMeasure E) (p q : E → ℝ) (eps : ℝ)
    (hp : Measurable p) (hq : Measurable q)
    (bp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (bq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    (per_env : ∀ e, |p e - q e| ≤ eps) :
    |(∫ₚ e, p e ∂(μ : Measure E)) - ∫ₚ e, q e ∂(μ : Measure E)| ≤ eps := by
  have heps : 0 ≤ eps := (abs_nonneg _).trans (per_env (Classical.choice μ.nonempty))
  have h₁ := expectation_le_add μ p q (fun _ => eps) hq (fun e => (bq e).1)
    (fun _ => heps) 1 eps (fun e => (bq e).2) (fun _ => le_rfl)
    (fun e => by have h := (abs_le.mp (per_env e)).2; linarith)
  have h₂ := expectation_le_add μ q p (fun _ => eps) hp (fun e => (bp e).1)
    (fun _ => heps) 1 eps (fun e => (bp e).2) (fun _ => le_rfl)
    (fun e => by have h := (abs_le.mp (per_env e)).1; linarith)
  rw [expectation_const μ eps heps] at h₁ h₂
  rw [abs_le]
  constructor <;> linarith

/-- Equal exact pushforwards transport expectations, on arbitrary spaces. -/
theorem expectation_eq_of_equal_laws
    {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) (f : X → Z) (g : Y → Z)
    (hf : Measurable f) (hg : Measurable g)
    (law : Measure.map f μ = Measure.map g ν)
    (test : Z → ℝ) (htest : Measurable test) :
    (∫ₚ x, test (f x) ∂μ) = ∫ₚ y, test (g y) ∂ν := by
  unfold expectation
  rw [← lintegral_map htest.ennreal_ofReal hf, law, lintegral_map htest.ennreal_ofReal hg]

#print axioms finite_of_bound
#print axioms expectation_const
#print axioms expectation_le_add
#print axioms average_bound
#print axioms expectation_eq_of_equal_laws
#print axioms decision_integrable
#print axioms decision_probability_bounds
end PV_MEAS_Average

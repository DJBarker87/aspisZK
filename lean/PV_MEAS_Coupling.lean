import PV_MEAS_Uniform
import PV_EVH_Interface

/-! Measured D163 coupling. Both marginals are exact pushforwards; the native
carrier and common sample may have unbounded or continuous support. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory PV_MEAS_Law
namespace PV_MEAS_Coupling
attribute [local instance] Classical.propDecidable
open PV_MEAS_Average PV_MEAS_Uniform

structure Coupling {R M : Type*} [MeasurableSpace R] [MeasurableSpace M]
    (μR : ProbabilityMeasure R) (μM : ProbabilityMeasure M) where
  S : Type
  [measurableS : MeasurableSpace S]
  law : ProbabilityMeasure S
  toR : S → R
  toM : S → M
  measurableR : Measurable toR
  measurableM : Measurable toM
  marginalR : Measure.map toR (law : Measure S) = (μR : Measure R)
  marginalM : Measure.map toM (law : Measure S) = (μM : Measure M)
attribute [instance] Coupling.measurableS

theorem integral_native {R M : Type*} [MeasurableSpace R] [MeasurableSpace M]
    {μR : ProbabilityMeasure R} {μM : ProbabilityMeasure M}
    (cp : Coupling μR μM) (f : R → ℝ) (hf : Measurable f) :
    (∫ₚ s, f (cp.toR s) ∂(cp.law : Measure cp.S)) = ∫ₚ r, f r ∂(μR : Measure R) := by
  unfold expectation
  rw [← lintegral_map hf.ennreal_ofReal cp.measurableR, cp.marginalR]

theorem integral_model {R M : Type*} [MeasurableSpace R] [MeasurableSpace M]
    {μR : ProbabilityMeasure R} {μM : ProbabilityMeasure M}
    (cp : Coupling μR μM) (f : M → ℝ) (hf : Measurable f) :
    (∫ₚ s, f (cp.toM s) ∂(cp.law : Measure cp.S)) = ∫ₚ r, f r ∂(μM : Measure M) := by
  unfold expectation
  rw [← lintegral_map hf.ennreal_ofReal cp.measurableM, cp.marginalM]

/-- Bounded decisions differ only on the original bad event. No truncation,
conditioning, or restriction on the sample carrier occurs. -/
theorem until_bad {S : Type*} [MeasurableSpace S] (μ : ProbabilityMeasure S)
    (f g b : S → ℝ) (hf : Measurable f) (hg : Measurable g) (hb : Measurable b)
    (bf : ∀ s, 0 ≤ f s ∧ f s ≤ 1) (bg : ∀ s, 0 ≤ g s ∧ g s ≤ 1)
    (bb : ∀ s, 0 ≤ b s ∧ b s ≤ 1)
    (control : ∀ s, |f s - g s| ≤ b s) :
    |(∫ₚ s, f s ∂(μ : Measure S)) - ∫ₚ s, g s ∂(μ : Measure S)| ≤
      ∫ₚ s, b s ∂(μ : Measure S) := by
  have h₁ := expectation_le_add μ f g b hg (fun s => (bg s).1) (fun s => (bb s).1)
    1 1 (fun s => (bg s).2) (fun s => (bb s).2)
    (fun s => by have h := (abs_le.mp (control s)).2; linarith)
  have h₂ := expectation_le_add μ g f b hf (fun s => (bf s).1) (fun s => (bb s).1)
    1 1 (fun s => (bf s).2) (fun s => (bb s).2)
    (fun s => by have h := (abs_le.mp (control s)).1; linarith)
  rw [abs_le]
  constructor <;> linarith

/-- Generic finite-model bridge, with arbitrary native and common laws.
The only finite carrier here is the retained cryptographic MODEL coordinate. -/
theorem finite_model_bound {R M : Type*} [MeasurableSpace R]
    [Fintype M] [Nonempty M] [MeasurableSpace M] [MeasurableSingletonClass M]
    (μR : ProbabilityMeasure R) (cp : Coupling μR (uniform M))
    (f : R → ℝ) (g : M → ℝ) (bad : M → Prop)
    (hf : Measurable f) (hg : Measurable g)
    (hb : Measurable (fun m => if bad m then (1 : ℝ) else 0))
    (bf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (bg : ∀ m, 0 ≤ g m ∧ g m ≤ 1)
    (agreement : ∀ s, ¬bad (cp.toM s) → f (cp.toR s) = g (cp.toM s)) :
    |(∫ₚ r, f r ∂(μR : Measure R)) - ∫ₚ m, g m ∂(uniform M : Measure M)| ≤
      ∫ₚ m, (if bad m then (1 : ℝ) else 0) ∂(uniform M : Measure M) := by
  classical
  have h := until_bad cp.law (fun s => f (cp.toR s)) (fun s => g (cp.toM s))
    (fun s => if bad (cp.toM s) then (1 : ℝ) else 0)
    (hf.comp cp.measurableR) (hg.comp cp.measurableM) (hb.comp cp.measurableM)
    (fun s => bf _) (fun s => bg _) (by intro s; split_ifs <;> norm_num)
    (by
      intro s
      by_cases hs : bad (cp.toM s)
      · rw [if_pos hs, abs_le]
        have h₁ := bf (cp.toR s); have h₂ := bg (cp.toM s)
        constructor <;> linarith
      · rw [if_neg hs, agreement s hs, sub_self, abs_zero])
  rw [integral_native cp f hf, integral_model cp g hg,
    integral_model cp (fun m => if bad m then (1 : ℝ) else 0) hb] at h
  exact h

#print axioms integral_native
#print axioms integral_model
#print axioms until_bad
#print axioms finite_model_bound
end PV_MEAS_Coupling

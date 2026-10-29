import PV_MEAS_Uniform
import R0Z.FsAbort
import R0Z.FsGood

set_option autoImplicit false
noncomputable section
open scoped ENNReal
open MeasureTheory PV_MEAS_Law
namespace PV_MEAS_Finite
attribute [local instance] Classical.propDecidable
open PV_MEAS_Uniform

/-- Exact bridge to the former rational uniform mean, with symbolic cardinality. -/
theorem integral_rat_mean {M : Type} [Fintype M] [Nonempty M]
    [MeasurableSpace M] [MeasurableSingletonClass M] (f : M → ℚ)
    (nonneg : ∀ m, 0 ≤ f m) :
    (∫ₚ m, (f m : ℝ) ∂(uniform M : Measure M)) = (R0Z.mean f : ℝ) := by
  rw [integral_uniform M _ (fun m => by exact_mod_cast nonneg m)]
  unfold R0Z.mean
  push_cast <;> rfl

theorem integral_bit_mean {M : Type} [Fintype M] [Nonempty M]
    [MeasurableSpace M] [MeasurableSingletonClass M] (f : M → Bool) :
    (∫ₚ m, (R0Z.FsStatement.bit (f m) : ℝ) ∂(uniform M : Measure M)) =
      (R0Z.mean (fun m => R0Z.FsStatement.bit (f m)) : ℝ) :=
  integral_rat_mean _ (fun _ => R0Z.FsGood.bit_nonneg _)

#print axioms integral_bit_mean
/-- Evaluation of a finite uniform measure, related exactly to rational mass. -/
theorem uniform_apply_real {X : Type} [Fintype X] [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (s : Set X) :
    ((uniform X : Measure X) s).toReal =
      (R0Z.mean (fun x => if x ∈ s then (1 : ℚ) else 0) : ℝ) := by
  classical
  change ((uniformMeasure X) s).toReal = _
  rw [uniformMeasure, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [ENNReal.toReal_sum (by intro a _; exact measure_ne_top _ _)]
  simp only [Measure.dirac_apply, Set.indicator_apply, Pi.one_apply]
  unfold R0Z.mean
  push_cast
  simp only [apply_ite, ENNReal.toReal_one, ENNReal.toReal_zero, div_eq_mul_inv]
  ring

/-- Exact rational test laws imply exact pushforward laws on finite uniform sources.
The output space is arbitrary; tests of measurable events identify the law. -/
theorem map_uniform_of_means {X Y Z : Type} [Fintype X] [Nonempty X]
    [Fintype Y] [Nonempty Y] [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y] [MeasurableSpace Z]
    (f : X → Z) (g : Y → Z) (hf : Measurable f) (hg : Measurable g)
    (law : ∀ test : Z → ℚ,
      R0Z.mean (fun x => test (f x)) = R0Z.mean (fun y => test (g y))) :
    Measure.map f (uniform X : Measure X) = Measure.map g (uniform Y : Measure Y) := by
  classical
  apply Measure.ext
  intro s hs
  have finite_f : (Measure.map f (uniform X : Measure X)) s ≠ ∞ := measure_ne_top _ _
  have finite_g : (Measure.map g (uniform Y : Measure Y)) s ≠ ∞ := measure_ne_top _ _
  apply (ENNReal.toReal_eq_toReal_iff' finite_f finite_g).mp
  rw [Measure.map_apply hf hs, Measure.map_apply hg hs, uniform_apply_real, uniform_apply_real]
  exact_mod_cast law (fun z => if z ∈ s then (1 : ℚ) else 0)

#print axioms uniform_apply_real
#print axioms map_uniform_of_means
#print axioms integral_rat_mean
end PV_MEAS_Finite

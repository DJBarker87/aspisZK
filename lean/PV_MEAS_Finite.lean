import PV_MEAS_Uniform
import R0Z.FsAbort

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace PV_MEAS_Finite
open PV_MEAS_Uniform

/-- Exact bridge to the former rational uniform mean, with symbolic cardinality. -/
theorem integral_rat_mean {M : Type} [Fintype M] [Nonempty M]
    [MeasurableSpace M] [MeasurableSingletonClass M] (f : M → ℚ) :
    (∫ m, (f m : ℝ) ∂(uniform M : Measure M)) = (R0Z.FsAbort.mean f : ℝ) := by
  rw [integral_uniform]
  unfold R0Z.FsAbort.mean
  push_cast
  rfl

#print axioms integral_rat_mean
end PV_MEAS_Finite

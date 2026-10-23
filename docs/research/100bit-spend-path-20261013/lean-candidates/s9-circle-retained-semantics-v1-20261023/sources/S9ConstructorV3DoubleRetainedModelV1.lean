import S9ConstructorV3DoubleSemanticsV1
import AspisFormal.V5FriNaturalBasisRadix4
import Mathlib.Tactic.Ring

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ConstructorV3DoubleRetainedModelV1
open AspisR1S9ConstructorV3QMMulSemanticsV1
open AspisCircleTensorBinding

/-- Symbolic one-step identity; no concrete recurrence is expanded. -/
theorem double_expr_eq_retained_model
    (x : AspisR1.ExtractedCurrentQM31Exact.QM31Exact) :
    x*x+x*x-1 = doubledFactor x 1 := by
  simp only [doubledFactor,pow_two]
  ring

/-- Same accepted actual constructor double call equals the retained
natural-circle evaluator's one-step doubling operation. -/
theorem generated_double_success_model (x z : SourceQM) (hx : Can x)
    (h : AspisR1S9ActualWeightsNewBoxNewV3.double x = .ok z) :
    Can z ∧ decode z = doubledFactor (decode x) 1 := by
  obtain ⟨hc,hd⟩ := AspisR1S9ConstructorV3DoubleSemanticsV1.generated_double_success_exact x z hx h
  exact ⟨hc,hd.trans (double_expr_eq_retained_model (decode x))⟩

/-- Two same-call doubling steps compose with the existing symbolic
addition theorem. This is the circle-factor loop's carry transition. -/
theorem generated_two_double_success_model (x y z : SourceQM) (hx : Can x)
    (hy : AspisR1S9ActualWeightsNewBoxNewV3.double x = .ok y)
    (hz : AspisR1S9ActualWeightsNewBoxNewV3.double y = .ok z) :
    Can z ∧ decode z = doubledFactor (decode x) 2 := by
  obtain ⟨hyc,hyd⟩ := generated_double_success_model x y hx hy
  obtain ⟨hzc,hzd⟩ := generated_double_success_model y z hyc hz
  refine ⟨hzc,?_⟩
  rw [hzd,hyd]
  exact (AspisV5FriNaturalBasisRadix4.doubledFactor_add (decode x) 1 1).symm

#print axioms double_expr_eq_retained_model
#print axioms generated_double_success_model
#print axioms generated_two_double_success_model
end AspisR1S9ConstructorV3DoubleRetainedModelV1

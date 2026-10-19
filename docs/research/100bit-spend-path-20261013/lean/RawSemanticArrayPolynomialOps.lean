import ExtractedSemanticRoundsCheckedTrace
import RawSemanticPolynomialOps

/-! Array-facing adapter for the actual 28-field Aeneas decode result. -/
set_option autoImplicit false

namespace AspisR1PublicPreparation.RawSemanticArrayPolynomialOps
open Aeneas Aeneas.Std
open RawSemanticPolynomialOps

variable {K : Type} [CommSemiring K]

noncomputable def decodedPolynomial (coefficients : Array K 28#usize) : Polynomial K :=
  polynomial coefficients.v

def decodedBoundary (coefficients : Array K 28#usize) : K :=
  sourceBoundary coefficients[0#usize] coefficients.v

def decodedValue (coefficients : Array K 28#usize) (x : K) : K :=
  sourceValue x coefficients.v

theorem array_head_eq_v_headD (coefficients : Array K 28#usize) :
    coefficients.v.headD 0 = coefficients[0#usize] := by
  cases coefficients with
  | mk values hlen =>
    cases values with
    | nil => simp at hlen
    | cons c cs => rfl

theorem decodedBoundary_eq_endpoint_sum (coefficients : Array K 28#usize) :
    decodedBoundary coefficients =
      (decodedPolynomial coefficients).eval 0 +
        (decodedPolynomial coefficients).eval 1 := by
  change sourceBoundary coefficients[0#usize] coefficients.v =
    (polynomial coefficients.v).eval 0 + (polynomial coefficients.v).eval 1
  rw [← array_head_eq_v_headD]
  exact sourceBoundary_eq_endpoint_sum coefficients.v

theorem decodedValue_eq_polynomial_eval (coefficients : Array K 28#usize) (x : K) :
    decodedValue coefficients x = (decodedPolynomial coefficients).eval x := by
  exact sourceValue_eq_polynomial_eval x coefficients.v

#print axioms decodedBoundary_eq_endpoint_sum
#print axioms decodedValue_eq_polynomial_eval

end AspisR1PublicPreparation.RawSemanticArrayPolynomialOps

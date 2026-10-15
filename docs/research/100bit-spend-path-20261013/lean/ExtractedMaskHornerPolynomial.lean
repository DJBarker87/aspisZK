import ExtractedMaskHornerLoop

/-! Symbolic closed form for the Nat-indexed model of the extracted reverse
Horner loop.  The generic theorem does not unfold any concrete coefficient
array or evaluate a fixed-size recurrence. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskHornerPolynomial

def hornerLoopModel {F : Type} [CommSemiring F]
    (coefficients : Nat → F) (x : F) : Nat → F → F
  | 0, acc => acc
  | n + 1, acc => hornerLoopModel coefficients x n
      (x * acc + coefficients n)

theorem hornerLoopModel_eq_sum {F : Type} [CommSemiring F]
    (coefficients : Nat → F) (x acc : F) (n : Nat) :
    hornerLoopModel coefficients x n acc =
      acc * x ^ n + ∑ i ∈ Finset.range n, coefficients i * x ^ i := by
  induction n generalizing acc with
  | zero => simp [hornerLoopModel]
  | succ n ih =>
      rw [hornerLoopModel, ih, Finset.sum_range_succ, pow_succ]
      ring

abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact

/-- The symbolic recurrence uses the same step function as the loop model
proved in `ExtractedMaskHornerLoop`; this is established structurally for all
lengths, not by reducing a fixed run. -/
theorem actual_model_eq_generic
    (coefficients : Nat → ExactQM) (linear : ExactQM)
    (n : Nat) (acc : ExactQM) :
    AspisR1.ExtractedMaskHornerLoop.hornerLoopModel coefficients linear n acc =
      hornerLoopModel coefficients linear n acc := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
      simp only [AspisR1.ExtractedMaskHornerLoop.hornerLoopModel,
        hornerLoopModel]
      exact ih (linear * acc + coefficients n)

def coefficientPolynomial (coefficients : Nat → ExactQM) (x : ExactQM) : ExactQM :=
  ∑ i ∈ Finset.range 27, coefficients i * x ^ i

/-- Keep the seed identity symbolic in the range length before specializing
it; this avoids reducing concrete finite sums or exact-field powers. -/
theorem generic_seed_coefficient_eq_sum {F : Type} [CommSemiring F]
    (coefficients : Nat → F) (x : F) (n : Nat) :
    hornerLoopModel coefficients x n (coefficients n) =
      ∑ i ∈ Finset.range (n + 1), coefficients i * x ^ i := by
  rw [hornerLoopModel_eq_sum, Finset.sum_range_succ]
  exact add_comm _ _

theorem generic_seed_coefficient_26_eq_polynomial
    (coefficients : Nat → ExactQM) (x : ExactQM) :
    hornerLoopModel coefficients x 26 (coefficients 26) =
      coefficientPolynomial coefficients x := by
  exact generic_seed_coefficient_eq_sum coefficients x 26

/-- The actual extracted-loop model, seeded by coefficient 26, equals the
degree-26 coefficient sum.  This remains a symbolic model result; it does not
establish how the runtime array is populated. -/
theorem seed_coefficient_26_eq_polynomial
    (coefficients : Nat → ExactQM) (x : ExactQM) :
    AspisR1.ExtractedMaskHornerLoop.hornerLoopModel coefficients x 26
        (coefficients 26) = coefficientPolynomial coefficients x := by
  calc
    AspisR1.ExtractedMaskHornerLoop.hornerLoopModel coefficients x 26
        (coefficients 26) = hornerLoopModel coefficients x 26
          (coefficients 26) := actual_model_eq_generic coefficients x 26 _
    _ = coefficientPolynomial coefficients x :=
      generic_seed_coefficient_26_eq_polynomial coefficients x

#print axioms hornerLoopModel_eq_sum
#print axioms actual_model_eq_generic
#print axioms generic_seed_coefficient_eq_sum
#print axioms generic_seed_coefficient_26_eq_polynomial
#print axioms seed_coefficient_26_eq_polynomial

end AspisR1.ExtractedMaskHornerPolynomial

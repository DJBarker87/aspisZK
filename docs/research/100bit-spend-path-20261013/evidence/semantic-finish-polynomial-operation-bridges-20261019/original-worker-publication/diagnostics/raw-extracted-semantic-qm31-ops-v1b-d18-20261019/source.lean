import ExtractedMaskQM31Exact
import RawSemanticPolynomialOps

/-! Refine the current extracted QM31 Result operation used by the semantic
boundary fold through the existing canonical-word homomorphism. This is a
machine-operation theorem for the pinned arithmetic-probe extraction; it does
not identify the abstract `RoundModel.Boundaries` implementation with that
probe. -/
set_option autoImplicit false

namespace AspisR1PublicPreparation.RawExtractedSemanticQM31Ops

open Aeneas Aeneas.Std Result
open AspisR1.ExtractedMaskQM31Exact

abbrev QM := AspisR1.ExtractedMaskQM31Exact.CurrentQM
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev ExactQM := AspisR1.ExtractedMaskQM31Exact.QM31Exact

def foldAdd : QM → List QM → Result QM
  | acc, [] => .ok acc
  | acc, x :: xs => do
      let next ← AspisR1Qm31ArithmeticProbe.field.QM31.add acc x
      foldAdd next xs

def semanticBoundaryResult (coefficients : List QM) : Result QM :=
  foldAdd (coefficients.headD AspisR1Qm31ArithmeticProbe.field.QM31.ZERO) coefficients

private theorem zero_canonical : Canonical AspisR1Qm31ArithmeticProbe.field.QM31.ZERO := by
  simp [Canonical, AspisR1.ExtractedMaskTowerAdd.CanonicalQM,
    AspisR1.ExtractedMaskTowerAdd.CanonicalCM,
    AspisR1Qm31ArithmeticProbe.field.QM31.ZERO,
    AspisR1.ExtractedMaskTowerAdd.P,
    AspisR1.ExtractedMaskM31AddSub.P]

private theorem decode_zero : decode AspisR1Qm31ArithmeticProbe.field.QM31.ZERO = (0 : ExactQM) := by
  ext <;> simp [decode, AspisR1Qm31ArithmeticProbe.field.QM31.ZERO]

theorem foldAdd_refines_sum (acc : QM) (coefficients : List QM)
    (hacc : Canonical acc) (hcoefficients : ∀ x ∈ coefficients, Canonical x) :
    ∃ out, foldAdd acc coefficients = .ok out ∧ Canonical out ∧
      decode out = decode acc + (coefficients.map decode).sum := by
  induction coefficients generalizing acc with
  | nil =>
      exact ⟨acc, rfl, hacc, by simp⟩
  | cons x xs ih =>
      have hx : Canonical x := hcoefficients x (by simp)
      have hxs : ∀ y ∈ xs, Canonical y := by
        intro y hy
        exact hcoefficients y (by simp [hy])
      obtain ⟨next, hnext, hnextCanonical, hnextDecode⟩ :=
        current_qm_add_exact acc x hacc hx
      obtain ⟨out, hout, houtCanonical, houtDecode⟩ :=
        ih next hnextCanonical hxs
      refine ⟨out, ?_, houtCanonical, ?_⟩
      · simp only [foldAdd, hnext, bind_tc_ok]
        exact hout
      · change decode out = decode acc + (decode x + (xs.map decode).sum)
        rw [houtDecode, hnextDecode]
        simp only [List.map_cons, List.sum_cons]
        rw [add_assoc]

theorem semanticBoundaryResult_refines (coefficients : List QM)
    (hcoefficients : ∀ x ∈ coefficients, Canonical x) :
    ∃ out, semanticBoundaryResult coefficients = .ok out ∧ Canonical out ∧
      decode out =
        AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceBoundary
          (decode (coefficients.headD AspisR1Qm31ArithmeticProbe.field.QM31.ZERO))
          (coefficients.map decode) := by
  have hseed : Canonical (coefficients.headD AspisR1Qm31ArithmeticProbe.field.QM31.ZERO) := by
    cases coefficients with
    | nil => exact zero_canonical
    | cons x xs => exact hcoefficients x (by simp)
  obtain ⟨out, hout, houtCanonical, hdecode⟩ :=
    foldAdd_refines_sum _ coefficients hseed hcoefficients
  refine ⟨out, hout, houtCanonical, ?_⟩
  rw [AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceBoundary_eq_seed_add_sum]
  exact hdecode

theorem semanticBoundaryResult_eq_polynomial_endpoints (coefficients : List QM)
    (hcoefficients : ∀ x ∈ coefficients, Canonical x) :
    ∃ out, semanticBoundaryResult coefficients = .ok out ∧ Canonical out ∧
      decode out =
        (AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial
          (coefficients.map decode)).eval 0 +
        (AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial
          (coefficients.map decode)).eval 1 := by
  obtain ⟨out, hout, houtCanonical, hdecode⟩ :=
    semanticBoundaryResult_refines coefficients hcoefficients
  refine ⟨out, hout, houtCanonical, ?_⟩
  have hzero :
      (coefficients.map decode).headD 0 =
        decode (coefficients.headD AspisR1Qm31ArithmeticProbe.field.QM31.ZERO) := by
    cases coefficients with
    | nil => simp [decode_zero]
    | cons x xs => rfl
  rw [← AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceBoundary_eq_endpoint_sum
    (coefficients.map decode)]
  rw [hzero]
  exact hdecode

#print axioms foldAdd_refines_sum
#print axioms semanticBoundaryResult_refines
#print axioms semanticBoundaryResult_eq_polynomial_endpoints

end AspisR1PublicPreparation.RawExtractedSemanticQM31Ops

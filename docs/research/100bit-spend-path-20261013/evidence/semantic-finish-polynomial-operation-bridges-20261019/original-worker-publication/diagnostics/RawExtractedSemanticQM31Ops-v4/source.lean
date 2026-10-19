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
      let next ← AspisR1SelectedMaskProbe.field.QM31.add acc x
      foldAdd next xs

def semanticBoundaryResult (coefficients : List QM) : Result QM :=
  foldAdd (coefficients.headD AspisR1SelectedMaskProbe.field.QM31.ZERO) coefficients

private theorem zero_canonical : Canonical AspisR1SelectedMaskProbe.field.QM31.ZERO := by
  simp [Canonical, AspisR1.ExtractedMaskTowerAdd.CanonicalQM,
    AspisR1.ExtractedMaskTowerAdd.CanonicalCM,
    AspisR1SelectedMaskProbe.field.QM31.ZERO,
    AspisR1.ExtractedMaskTowerAdd.P,
    AspisR1.ExtractedMaskM31AddSub.P]

private theorem decode_zero : decode AspisR1SelectedMaskProbe.field.QM31.ZERO = (0 : ExactQM) := by
  ext <;> simp [decode, AspisR1SelectedMaskProbe.field.QM31.ZERO]

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
      · simpa [foldAdd, hnext] using hout
      · change decode out = decode acc + (decode x + (xs.map decode).sum)
        rw [houtDecode, hnextDecode]
        rw [add_assoc]

theorem semanticBoundaryResult_refines (coefficients : List QM)
    (hcoefficients : ∀ x ∈ coefficients, Canonical x) :
    ∃ out, semanticBoundaryResult coefficients = .ok out ∧ Canonical out ∧
      decode out =
        AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceBoundary
          (decode (coefficients.headD AspisR1SelectedMaskProbe.field.QM31.ZERO))
          (coefficients.map decode) := by
  have hseed : Canonical (coefficients.headD AspisR1SelectedMaskProbe.field.QM31.ZERO) := by
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
        decode (coefficients.headD AspisR1SelectedMaskProbe.field.QM31.ZERO) := by
    cases coefficients with
    | nil => simp [decode_zero]
    | cons x xs => rfl
  rw [← hzero] at hdecode
  calc
    decode out = AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceBoundary
        ((coefficients.map decode).headD 0) (coefficients.map decode) := hdecode
    _ = (AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial
          (coefficients.map decode)).eval 0 +
        (AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial
          (coefficients.map decode)).eval 1 :=
      AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceBoundary_eq_endpoint_sum
        (coefficients.map decode)


/-- Fixed-size array adapter. Its `.v` list is exactly the iterator order used by
Rust's copied array fold, and the theorem projects each machine field operation
through the retained exact decoder. -/
def semanticBoundaryArrayResult (coefficients : Array QM 28#usize) : Result QM :=
  semanticBoundaryResult coefficients.v

theorem semanticBoundaryArrayResult_eq_polynomial_endpoints
    (coefficients : Array QM 28#usize)
    (hcoefficients : ∀ x ∈ coefficients.v, Canonical x) :
    ∃ out, semanticBoundaryArrayResult coefficients = .ok out ∧ Canonical out ∧
      decode out =
        (AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial
          (coefficients.v.map decode)).eval 0 +
        (AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial
          (coefficients.v.map decode)).eval 1 := by
  obtain ⟨out, hout, hcanonical, hvalue⟩ :=
    semanticBoundaryResult_eq_polynomial_endpoints coefficients.v hcoefficients
  exact ⟨out, hout, hcanonical, hvalue⟩


#print axioms foldAdd_refines_sum
#print axioms semanticBoundaryResult_refines
#print axioms semanticBoundaryResult_eq_polynomial_endpoints
#print axioms semanticBoundaryArrayResult_eq_polynomial_endpoints

end AspisR1PublicPreparation.RawExtractedSemanticQM31Ops

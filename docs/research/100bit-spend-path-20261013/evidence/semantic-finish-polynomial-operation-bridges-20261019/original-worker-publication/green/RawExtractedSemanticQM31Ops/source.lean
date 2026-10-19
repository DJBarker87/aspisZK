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


/-- Exact one-step counterpart of the reverse Horner loop: multiply the
running accumulator by the challenge, then add the current coefficient. -/
def hornerFold (alpha : QM) : List QM → Result QM
  | [] => .ok AspisR1SelectedMaskProbe.field.QM31.ZERO
  | c :: cs => do
      let acc ← hornerFold alpha cs
      let product ← AspisR1SelectedMaskProbe.field.QM31.mul acc alpha
      AspisR1SelectedMaskProbe.field.QM31.add product c

private theorem sourceValue_cons (x c : ExactQM) (cs : List ExactQM) :
    AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceValue x (c :: cs) =
      AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceValue x cs * x + c := by
  rw [AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceValue_eq_lowHorner]
  change AspisR1PublicPreparation.RawSemanticPolynomialOps.lowHorner x (c :: cs) = _
  rw [show AspisR1PublicPreparation.RawSemanticPolynomialOps.lowHorner x (c :: cs) =
    c + x * AspisR1PublicPreparation.RawSemanticPolynomialOps.lowHorner x cs by rfl]
  rw [← AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceValue_eq_lowHorner]
  rw [mul_comm x (AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceValue x cs), add_comm]

/-- Every step of the extracted Result-returning reverse Horner fold succeeds
on canonical operands, and its projection is the mathematical fold. -/
theorem hornerFold_refines (alpha : QM) (coefficients : List QM)
    (halpha : Canonical alpha)
    (hcoefficients : ∀ x ∈ coefficients, Canonical x) :
    ∃ out, hornerFold alpha coefficients = .ok out ∧ Canonical out ∧
      decode out =
        AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceValue
          (decode alpha) (coefficients.map decode) := by
  induction coefficients with
  | nil =>
      refine ⟨AspisR1SelectedMaskProbe.field.QM31.ZERO, rfl, zero_canonical, ?_⟩
      change decode AspisR1SelectedMaskProbe.field.QM31.ZERO = 0
      exact decode_zero
  | cons c cs ih =>
      have hc : Canonical c := hcoefficients c (by simp)
      have hcs : ∀ x ∈ cs, Canonical x := by
        intro x hx
        exact hcoefficients x (by simp [hx])
      obtain ⟨acc, hacc, haccCanonical, haccDecode⟩ := ih hcs
      obtain ⟨product, hmul, hproductCanonical, hproductDecode⟩ :=
        current_qm_mul_exact acc alpha haccCanonical halpha
      obtain ⟨out, hadd, houtCanonical, houtDecode⟩ :=
        current_qm_add_exact product c hproductCanonical hc
      refine ⟨out, ?_, houtCanonical, ?_⟩
      · simp [hornerFold, hacc, hmul, hadd]
      · change decode out =
          AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceValue
            (decode alpha) ((c :: cs).map decode)
        calc
          decode out = decode product + decode c := houtDecode
          _ = decode acc * decode alpha + decode c := by rw [hproductDecode]
          _ = AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceValue
                (decode alpha) (cs.map decode) * decode alpha + decode c := by
              rw [haccDecode]
          _ = AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceValue
                (decode alpha) ((c :: cs).map decode) := by
              rw [List.map_cons, sourceValue_cons]

/-- The actual extracted reverse Horner loop projects to evaluation at its
challenge, via the existing polynomial identity. -/
theorem hornerFold_refines_polynomial_eval (alpha : QM) (coefficients : List QM)
    (halpha : Canonical alpha)
    (hcoefficients : ∀ x ∈ coefficients, Canonical x) :
    ∃ out, hornerFold alpha coefficients = .ok out ∧ Canonical out ∧
      decode out =
        (AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial
          (coefficients.map decode)).eval (decode alpha) := by
  obtain ⟨out, hout, hcanonical, hvalue⟩ :=
    hornerFold_refines alpha coefficients halpha hcoefficients
  exact ⟨out, hout, hcanonical,
    hvalue.trans (AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceValue_eq_polynomial_eval
      (decode alpha) (coefficients.map decode))⟩

/-- Fixed-size array adapter for the copied reverse Horner traversal. -/
def hornerArrayResult (alpha : QM) (coefficients : Array QM 28#usize) : Result QM :=
  hornerFold alpha coefficients.v

theorem hornerArrayResult_refines_polynomial_eval (alpha : QM)
    (coefficients : Array QM 28#usize) (halpha : Canonical alpha)
    (hcoefficients : ∀ x ∈ coefficients.v, Canonical x) :
    ∃ out, hornerArrayResult alpha coefficients = .ok out ∧ Canonical out ∧
      decode out =
        (AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial
          (coefficients.v.map decode)).eval (decode alpha) := by
  obtain ⟨out, hout, hcanonical, hvalue⟩ :=
    hornerFold_refines_polynomial_eval alpha coefficients.v halpha hcoefficients
  exact ⟨out, hout, hcanonical, hvalue⟩

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
#print axioms hornerFold_refines
#print axioms hornerFold_refines_polynomial_eval
#print axioms hornerArrayResult_refines_polynomial_eval

end AspisR1PublicPreparation.RawExtractedSemanticQM31Ops

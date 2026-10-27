import AspisR1SemanticCallExtraction.Funs
import RPt_JFv_RawExtractedSemanticBoundaryLoopV7
import RPt_JFv_RawExtractedSemanticValueLoopV1
import RPt_JFv_RawSemanticPolynomialOps

set_option autoImplicit false
namespace AspisR1PublicPreparation.RawExtractedSemanticPolynomialWrappersV1

open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
open AspisR1.ExtractedMaskQM31Exact

abbrev GenQ := AspisR1SemanticCallExtraction.aspis_core.field.QM31
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM

private theorem array_index_usize_ok {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (hi : i.val < n.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

theorem semantic_boundary_refines_polynomial_endpoints
    (p : Array GenQ 28#usize)
    (hp : ∀ i : Nat, (hi : i < 28) →
      Canonical (genQToProbe (p.val[i]'(by simpa [p.property] using hi)))) :
    ∃ out : GenQ,
      AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary p = .ok out ∧
      Canonical (genQToProbe out) ∧
      decode (genQToProbe out) =
        (AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial
          (AspisR1PublicPreparation.RawExtractedSemanticBoundaryLoopV7.coefficients p)).eval 0 +
        (AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial
          (AspisR1PublicPreparation.RawExtractedSemanticBoundaryLoopV7.coefficients p)).eval 1 := by
  let seed : GenQ := p.val[0]'(by simpa [p.property])
  have hseedCanonical : Canonical (genQToProbe seed) := hp 0 (by decide)
  have hseedRead : Array.index_usize p 0#usize = .ok seed := by
    simpa [seed] using array_index_usize_ok p 0#usize (by decide)
  obtain ⟨out, hloop, hcanonical, hdecode⟩ :=
    AspisR1PublicPreparation.RawExtractedSemanticBoundaryLoopV7.semantic_boundary_loop_refines
      p seed hseedCanonical hp
  refine ⟨out, ?_, hcanonical, ?_⟩
  · simp only [AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary,
      hseedRead, bind_tc_ok]
    exact hloop
  · have hseed : decode (genQToProbe seed) =
        (AspisR1PublicPreparation.RawExtractedSemanticBoundaryLoopV7.coefficients p).headD 0 := by
      have hhead : p.val.head? = some seed := by
        rw [List.head?_eq_getElem?]
        simp [seed, p.property]
      simp [AspisR1PublicPreparation.RawExtractedSemanticBoundaryLoopV7.coefficients,
        List.headD_eq_head?_getD, List.head?_map, hhead, seed]
    calc
      decode (genQToProbe out) = decode (genQToProbe seed) +
          (AspisR1PublicPreparation.RawExtractedSemanticBoundaryLoopV7.coefficients p).sum := hdecode
      _ = AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceBoundary
            (decode (genQToProbe seed))
            (AspisR1PublicPreparation.RawExtractedSemanticBoundaryLoopV7.coefficients p) :=
        (AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceBoundary_eq_seed_add_sum _ _).symm
      _ = AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceBoundary
            ((AspisR1PublicPreparation.RawExtractedSemanticBoundaryLoopV7.coefficients p).headD 0)
            (AspisR1PublicPreparation.RawExtractedSemanticBoundaryLoopV7.coefficients p) := by rw [hseed]
      _ =
          (AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial
            (AspisR1PublicPreparation.RawExtractedSemanticBoundaryLoopV7.coefficients p)).eval 0 +
          (AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial
            (AspisR1PublicPreparation.RawExtractedSemanticBoundaryLoopV7.coefficients p)).eval 1 :=
        AspisR1PublicPreparation.RawSemanticPolynomialOps.sourceBoundary_eq_endpoint_sum
          (AspisR1PublicPreparation.RawExtractedSemanticBoundaryLoopV7.coefficients p)

#print axioms semantic_boundary_refines_polynomial_endpoints
#print axioms AspisR1PublicPreparation.RawExtractedSemanticValueLoopV1.semantic_value_refines_polynomial_eval
end AspisR1PublicPreparation.RawExtractedSemanticPolynomialWrappersV1

import S1ExtractedRoundChildrenV1
import RawExtractedSemanticPolynomialWrappersV1
set_option autoImplicit false
namespace AspisS1ExtractedRoundChildren
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

def Canonical (q : MainQM) : Prop :=
  AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM (genQToProbe (mainToGen q))

/-- TOTAL on canonical coefficient arrays, reusing the checked source-loop
arithmetic theorem. No accepted-child-success premise is assumed. This is
not a totality claim about arbitrary noncanonical native words. -/
theorem boundary_total_canonical (p : Array MainQM 28#usize)
    (hp : ∀ q ∈ p.val, Canonical q) :
    ∃ out, children.boundary p = ok out ∧ Canonical out := by
  have hcoeff : ∀ i : Nat, (hi : i < 28) →
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
        (genQToProbe ((mainArrayToGen p).val[i]'(by simpa [mainArrayToGen] using hi))) := by
    intro i hi
    have himem := hp (p.val[i]'(by simpa [p.property] using hi)) (List.getElem_mem _)
    simpa only [Canonical, mainArrayToGen, List.getElem_map] using himem
  obtain ⟨out, call, canon, _⟩ :=
    AspisR1PublicPreparation.RawExtractedSemanticPolynomialWrappersV1.semantic_boundary_refines_polynomial_endpoints
      (mainArrayToGen p) hcoeff
  refine ⟨genToMain out, ?_, ?_⟩
  · change genResultToMain
      (AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary_entry (mainArrayToGen p)) = _
    simpa only [AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary_entry,
      call, genResultToMain, bind_tc_ok]
  · cases out with
    | mk c0 c1 => cases c0; cases c1; exact canon

/-- TOTAL on canonical reached inputs with round<10; all checked loop index
and arithmetic operations are included in the reused theorem. -/
theorem value_total_canonical (p : Array MainQM 28#usize)
    (a : Array MainQM 10#usize) (round : Usize) (hr : round.val < 10)
    (hp : ∀ q ∈ p.val, Canonical q) (ha : ∀ q ∈ a.val, Canonical q) :
    ∃ out, children.value p a round = ok out ∧ Canonical out := by
  have hcoeff : ∀ i : Nat, (hi : i < 28) →
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
        (genQToProbe ((mainArrayToGen p).val[i]'(by simpa [mainArrayToGen] using hi))) := by
    intro i hi
    have himem := hp (p.val[i]'(by simpa [p.property] using hi)) (List.getElem_mem _)
    simpa only [Canonical, mainArrayToGen, List.getElem_map] using himem
  have halpha : AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
      (genQToProbe ((mainAlphaArrayToGen a).val[round.val]'(by simpa [mainAlphaArrayToGen] using hr))) := by
    have himem := ha (a.val[round.val]'(by simpa [a.property] using hr)) (List.getElem_mem _)
    simpa only [Canonical, mainAlphaArrayToGen, List.getElem_map] using himem
  obtain ⟨out, call, canon, _⟩ :=
    AspisR1PublicPreparation.RawExtractedSemanticValueLoopV1.semantic_value_refines_polynomial_eval
      (mainArrayToGen p) (mainAlphaArrayToGen a) round hr halpha hcoeff
  refine ⟨genToMain out, ?_, ?_⟩
  · change genResultToMain
      (AspisR1SemanticCallExtraction.r1_semantic.semantic_value_entry
        (mainArrayToGen p) (mainAlphaArrayToGen a) round) = _
    simpa only [AspisR1SemanticCallExtraction.r1_semantic.semantic_value_entry,
      call, genResultToMain, bind_tc_ok]
  · cases out with
    | mk c0 c1 => cases c0; cases c1; exact canon

#print axioms boundary_total_canonical
#print axioms value_total_canonical
end AspisS1ExtractedRoundChildren

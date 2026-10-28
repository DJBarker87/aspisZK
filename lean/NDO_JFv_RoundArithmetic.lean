import NDO_JFv_DecodeCanonical
import RPu_JFv_RawExtractedSemanticPolynomialWrappersV1
set_option autoImplicit false
namespace AspisR1.JFv_RoundArithmetic
open Aeneas Aeneas.Std Result
open AspisS1ExtractedRoundChildren
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
open AspisR1.ExtractedMaskQM31Exact

def Canonical (q : MainQM) : Prop := CurrentCanonicalQM (genQToProbe (mainToGen q))

theorem boundary (p : Array MainQM 28#usize)
    (hp : ∀ i : Fin 28, Canonical (p.val[i.val]'(by simpa only [p.property,show (28#usize).val=28 from rfl] using i.isLt))) :
    ∃ out,generatedMainBoundary p=ok out ∧ Canonical out := by
  have canon : ∀ i : Nat,(hi : i<28) → CurrentCanonicalQM
      (genQToProbe ((mainArrayToGen p).val[i]'(by simp only [mainArrayToGen,List.length_map,p.property];exact hi))) := by
    intro i hi
    simpa only [Canonical,mainArrayToGen,List.getElem_map] using hp ⟨i,hi⟩
  obtain ⟨out,call,canonical,_⟩ :=
    AspisR1PublicPreparation.RawExtractedSemanticPolynomialWrappersV1.semantic_boundary_refines_polynomial_endpoints
      (mainArrayToGen p) canon
  refine ⟨genToMain out,?_,?_⟩
  · unfold generatedMainBoundary AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary_entry
    rw [call];rfl
  · simpa only [Canonical,mainToGen,genToMain] using canonical

theorem value (p : Array MainQM 28#usize) (alpha : Array MainQM 10#usize) (round : Usize)
    (hr : round.val<10)
    (ha : Canonical (alpha.val[round.val]'(by simpa only [alpha.property,show (10#usize).val=10 from rfl] using hr)))
    (hp : ∀ i : Fin 28, Canonical (p.val[i.val]'(by simpa only [p.property,show (28#usize).val=28 from rfl] using i.isLt))) :
    ∃ out,generatedMainValue p alpha round=ok out ∧ Canonical out := by
  have canon : ∀ i : Nat,(hi : i<28) → CurrentCanonicalQM
      (genQToProbe ((mainArrayToGen p).val[i]'(by simp only [mainArrayToGen,List.length_map,p.property];exact hi))) := by
    intro i hi
    simpa only [Canonical,mainArrayToGen,List.getElem_map] using hp ⟨i,hi⟩
  have ac : CurrentCanonicalQM (genQToProbe ((mainAlphaArrayToGen alpha).val[round.val]'(by
      simp only [mainAlphaArrayToGen,List.length_map,alpha.property];exact hr))) := by
    simpa only [Canonical,mainAlphaArrayToGen,List.getElem_map] using ha
  obtain ⟨out,call,canonical,_⟩ :=
    AspisR1PublicPreparation.RawExtractedSemanticValueLoopV1.semantic_value_refines_polynomial_eval
      (mainArrayToGen p) (mainAlphaArrayToGen alpha) round hr ac canon
  refine ⟨genToMain out,?_,?_⟩
  · unfold generatedMainValue AspisR1SemanticCallExtraction.r1_semantic.semantic_value_entry
    rw [call];rfl
  · simpa only [Canonical,mainToGen,genToMain] using canonical

#print axioms boundary
#print axioms value
end AspisR1.JFv_RoundArithmetic

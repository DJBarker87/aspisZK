import NDO_JFr_Boundary03
import NDO_JFr_Horner03_0
import NDO_JFr_Horner03_1
import NDO_JFv_RoundArithmetic
set_option autoImplicit false
namespace AspisR1.JFr_Round03
open Aeneas Aeneas.Std Result
open JFr_Data03 AspisS1ExtractedRoundChildren

def polynomial : Array MainQM 28#usize := ⟨p.val.map genToMain,by simp only [List.length_map,p.property]⟩
def challenges : Array MainQM 10#usize := ⟨alpha.val.map genToMain,by simp only [List.length_map,alpha.property]⟩

theorem horner : AspisR1SemanticCallExtraction.r1_semantic.semantic_value p alpha 3#usize=ok output := by
  have joined := JFr_HornerTrace.append JFr_Horner03_0.trace JFr_Horner03_1.trace
  have zero : JFr_Horner03_0.initial=AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO := by
    unfold JFr_Horner03_0.initial JFr_WordArithmetic.q AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO
    rfl
  have last : JFr_Horner03_1.final=output := rfl
  rw [zero,last] at joined
  exact JFr_HornerTrace.source joined (by change ¬0>0; omega)

theorem boundary : generatedMainBoundary polynomial=ok (genToMain running) := by
  unfold generatedMainBoundary AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary_entry
  have same : mainArrayToGen polynomial=p := rfl
  rw [same,JFr_Boundary03.source]
  rfl

theorem value : generatedMainValue polynomial challenges 3#usize=ok (genToMain output) := by
  unfold generatedMainValue AspisR1SemanticCallExtraction.r1_semantic.semantic_value_entry
  have same : mainArrayToGen polynomial=p := rfl
  have alphaSame : mainAlphaArrayToGen challenges=alpha := rfl
  rw [same,alphaSame,horner]
  rfl

#print axioms horner
#print axioms boundary
#print axioms value
end AspisR1.JFr_Round03

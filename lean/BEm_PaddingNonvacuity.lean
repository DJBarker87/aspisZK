import BEm_PaddingCut
set_option autoImplicit false
namespace AspisR1.BEm_PaddingNonvacuity
open BEm_PaddingModel

def zeroWord : Word := ⟨0,0,0,0,0,0,0,0⟩
def oneWord : Word := ⟨1,0,0,0,0,0,0,0⟩

/-- Local padding model has both accepted zero words and rejected nonzero
words. This is not a joint deployment/security-game realization. -/
theorem branches :
    valid zeroWord ∧ valid oneWord ∧
    nativeWord zeroWord = false ∧ referenceWord zeroWord = false ∧
    nativeWord oneWord = true ∧ referenceWord oneWord = true := by
  have v0 : valid zeroWord := by simp [valid,bytes,zeroWord]
  have v1 : valid oneWord := by simp [valid,bytes,oneWord]
  refine ⟨v0,v1,?_,rfl,?_,rfl⟩
  · rw [BEm_PaddingModel.word _ v0]
    rfl
  · rw [BEm_PaddingModel.word _ v1]
    rfl

#print axioms branches
end AspisR1.BEm_PaddingNonvacuity

import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk26

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk27
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk26

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat113_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨113,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨113,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨105,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row337]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨113,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 104 ∧ (colOrder j).val ≠ 105 ∧ (colOrder j).val ≠ 106 ∧ (colOrder j).val ≠ 108 ∧ (colOrder j).val ≠ 112 := by decide
  simp only [literalRow337, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2]

#print axioms rowFlat113_lower_zero

theorem rowFlat114_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨114,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨114,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨106,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row339]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨114,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 105 ∧ (colOrder j).val ≠ 106 := by decide
  simp only [literalRow339, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat114_lower_zero

theorem rowFlat115_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨115,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨115,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨107,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row341]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨115,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 106 ∧ (colOrder j).val ≠ 107 ∧ (colOrder j).val ≠ 108 := by decide
  simp only [literalRow341, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat115_lower_zero

theorem rowFlat116_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨116,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨116,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨108,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row343]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨116,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 107 ∧ (colOrder j).val ≠ 108 := by decide
  simp only [literalRow343, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat116_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk27

import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk21

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk22
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk21

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat79_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨79,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨79,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨85,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row295]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨79,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 84 ∧ (colOrder j).val ≠ 85 := by decide
  simp only [literalRow295, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat79_lower_zero

theorem rowFlat80_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨80,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨80,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨86,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row297]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨80,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 85 ∧ (colOrder j).val ≠ 86 ∧ (colOrder j).val ≠ 87 ∧ (colOrder j).val ≠ 89 := by decide
  simp only [literalRow297, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat80_lower_zero

theorem rowFlat81_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨81,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨81,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨87,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row299]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨81,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 86 ∧ (colOrder j).val ≠ 87 := by decide
  simp only [literalRow299, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat81_lower_zero

theorem rowFlat82_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨82,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨82,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨88,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row301]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨82,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 87 ∧ (colOrder j).val ≠ 88 ∧ (colOrder j).val ≠ 89 := by decide
  simp only [literalRow301, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat82_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk22

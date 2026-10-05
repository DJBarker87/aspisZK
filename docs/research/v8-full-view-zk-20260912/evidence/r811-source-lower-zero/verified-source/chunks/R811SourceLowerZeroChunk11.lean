import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk10

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk11
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk10

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat47_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨47,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨47,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨41,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row204]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨47,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 39 ∧ (colOrder j).val ≠ 40 ∧ (colOrder j).val ≠ 41 ∧ (colOrder j).val ≠ 42 := by decide
  simp only [literalRow204, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat47_lower_zero

theorem rowFlat48_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨48,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨48,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨42,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row206]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨48,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 41 ∧ (colOrder j).val ≠ 42 := by decide
  simp only [literalRow206, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat48_lower_zero

theorem rowFlat49_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨49,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨49,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨43,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row208]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨49,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 41 ∧ (colOrder j).val ≠ 42 ∧ (colOrder j).val ≠ 43 ∧ (colOrder j).val ≠ 44 ∧ (colOrder j).val ≠ 45 ∧ (colOrder j).val ≠ 46 ∧ (colOrder j).val ≠ 49 ∧ (colOrder j).val ≠ 50 := by decide
  simp only [literalRow208, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2.2]

#print axioms rowFlat49_lower_zero

theorem rowFlat50_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨50,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨50,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨44,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row210]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨50,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 43 ∧ (colOrder j).val ≠ 44 := by decide
  simp only [literalRow210, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat50_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk11

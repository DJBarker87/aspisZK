import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk38

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk39
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk38

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat158_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨158,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨158,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨153,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row890]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨158,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 152 ∧ (colOrder j).val ≠ 153 := by decide
  simp only [literalRow890, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat158_lower_zero

theorem rowFlat159_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨159,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨159,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨154,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row892]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨159,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 152 ∧ (colOrder j).val ≠ 153 ∧ (colOrder j).val ≠ 154 ∧ (colOrder j).val ≠ 155 := by decide
  simp only [literalRow892, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat159_lower_zero

theorem rowFlat160_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨160,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨160,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨155,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row894]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨160,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 154 ∧ (colOrder j).val ≠ 155 := by decide
  simp only [literalRow894, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat160_lower_zero

theorem rowFlat188_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨188,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨188,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨156,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row900]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨188,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 156 ∧ (colOrder j).val ≠ 157 := by decide
  simp only [literalRow900, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat188_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk39

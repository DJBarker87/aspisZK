import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk34

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk35
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk34

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat145_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨145,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨145,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨137,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row632]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨145,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 135 ∧ (colOrder j).val ≠ 136 ∧ (colOrder j).val ≠ 137 ∧ (colOrder j).val ≠ 138 ∧ (colOrder j).val ≠ 139 ∧ (colOrder j).val ≠ 140 := by decide
  simp only [literalRow632, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2]

#print axioms rowFlat145_lower_zero

theorem rowFlat146_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨146,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨146,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨138,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row634]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨146,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 137 ∧ (colOrder j).val ≠ 138 ∧ (colOrder j).val ≠ 141 := by decide
  simp only [literalRow634, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat146_lower_zero

theorem rowFlat147_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨147,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨147,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨139,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row636]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨147,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 137 ∧ (colOrder j).val ≠ 138 ∧ (colOrder j).val ≠ 139 ∧ (colOrder j).val ≠ 140 ∧ (colOrder j).val ≠ 141 := by decide
  simp only [literalRow636, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2]

#print axioms rowFlat147_lower_zero

theorem rowFlat148_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨148,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨148,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨140,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row638]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨148,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 139 ∧ (colOrder j).val ≠ 140 ∧ (colOrder j).val ≠ 141 := by decide
  simp only [literalRow638, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat148_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk35

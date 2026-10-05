import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk18

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk19
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk18

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat91_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨91,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨91,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨73,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row271]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨91,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 72 ∧ (colOrder j).val ≠ 73 := by decide
  simp only [literalRow271, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat91_lower_zero

theorem rowFlat92_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨92,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨92,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨74,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row273]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨92,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 73 ∧ (colOrder j).val ≠ 74 ∧ (colOrder j).val ≠ 75 ∧ (colOrder j).val ≠ 77 ∧ (colOrder j).val ≠ 81 := by decide
  simp only [literalRow273, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2]

#print axioms rowFlat92_lower_zero

theorem rowFlat93_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨93,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨93,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨75,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row275]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨93,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 74 ∧ (colOrder j).val ≠ 75 := by decide
  simp only [literalRow275, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat93_lower_zero

theorem rowFlat94_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨94,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨94,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨76,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row277]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨94,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 75 ∧ (colOrder j).val ≠ 76 ∧ (colOrder j).val ≠ 77 := by decide
  simp only [literalRow277, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat94_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk19

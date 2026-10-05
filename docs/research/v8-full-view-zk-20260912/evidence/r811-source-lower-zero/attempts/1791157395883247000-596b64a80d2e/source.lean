import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk12

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk13
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk12

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat55_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨55,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨55,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨49,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row220]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨55,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 47 ∧ (colOrder j).val ≠ 48 ∧ (colOrder j).val ≠ 49 ∧ (colOrder j).val ≠ 50 := by decide
  simp only [literalRow220, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat55_lower_zero

theorem rowFlat56_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨56,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨56,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨50,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row222]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨56,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 49 ∧ (colOrder j).val ≠ 50 := by decide
  simp only [literalRow222, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat56_lower_zero

theorem rowFlat57_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨57,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨57,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨51,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row224]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨57,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 49 ∧ (colOrder j).val ≠ 50 ∧ (colOrder j).val ≠ 51 ∧ (colOrder j).val ≠ 52 ∧ (colOrder j).val ≠ 53 ∧ (colOrder j).val ≠ 54 ∧ (colOrder j).val ≠ 57 ∧ (colOrder j).val ≠ 58 ∧ (colOrder j).val ≠ 65 := by decide
  simp only [literalRow224, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2.2.2]

#print axioms rowFlat57_lower_zero

theorem rowFlat58_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨58,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨58,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨52,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row226]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨58,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 51 ∧ (colOrder j).val ≠ 52 := by decide
  simp only [literalRow226, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat58_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk13

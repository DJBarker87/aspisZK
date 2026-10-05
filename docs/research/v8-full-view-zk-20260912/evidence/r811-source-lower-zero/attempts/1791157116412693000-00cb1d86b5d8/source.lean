import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk01

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk02
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk01

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat40_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨40,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨40,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨5,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row124]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨40,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 3 ∧ (colOrder j).val ≠ 4 ∧ (colOrder j).val ≠ 5 ∧ (colOrder j).val ≠ 6 := by decide
  simp only [literalRow124, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat40_lower_zero

theorem rowFlat41_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨41,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨41,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨6,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row126]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨41,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 5 ∧ (colOrder j).val ≠ 6 := by decide
  simp only [literalRow126, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat41_lower_zero

theorem rowFlat18_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨18,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨18,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨7,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row128]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨18,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 5 ∧ (colOrder j).val ≠ 6 ∧ (colOrder j).val ≠ 7 ∧ (colOrder j).val ≠ 8 ∧ (colOrder j).val ≠ 9 ∧ (colOrder j).val ≠ 10 ∧ (colOrder j).val ≠ 13 ∧ (colOrder j).val ≠ 14 ∧ (colOrder j).val ≠ 21 ∧ (colOrder j).val ≠ 22 ∧ (colOrder j).val ≠ 35 ∧ (colOrder j).val ≠ 65 := by decide
  simp only [literalRow128, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2.2.2.2.2.2]

#print axioms rowFlat18_lower_zero

theorem rowFlat19_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨19,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨19,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨8,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row130]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨19,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 7 ∧ (colOrder j).val ≠ 8 ∧ (colOrder j).val ≠ 221 := by decide
  simp only [literalRow130, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat19_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk02

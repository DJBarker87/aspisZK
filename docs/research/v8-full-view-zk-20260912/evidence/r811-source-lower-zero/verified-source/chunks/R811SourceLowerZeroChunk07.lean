import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk06

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk07
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk06

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat12_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨12,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨12,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨25,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row164]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨12,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 23 ∧ (colOrder j).val ≠ 24 ∧ (colOrder j).val ≠ 25 ∧ (colOrder j).val ≠ 26 := by decide
  simp only [literalRow164, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat12_lower_zero

theorem rowFlat13_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨13,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨13,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨26,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row166]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨13,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 25 ∧ (colOrder j).val ≠ 26 := by decide
  simp only [literalRow166, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat13_lower_zero

theorem rowFlat14_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨14,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨14,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨27,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row168]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨14,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 25 ∧ (colOrder j).val ≠ 26 ∧ (colOrder j).val ≠ 27 ∧ (colOrder j).val ≠ 28 ∧ (colOrder j).val ≠ 29 ∧ (colOrder j).val ≠ 30 := by decide
  simp only [literalRow168, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2]

#print axioms rowFlat14_lower_zero

theorem rowFlat15_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨15,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨15,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨28,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row170]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨15,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 27 ∧ (colOrder j).val ≠ 28 := by decide
  simp only [literalRow170, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat15_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk07

import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk02

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk03
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk02

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat20_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨20,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨20,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨9,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row132]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨20,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 7 ∧ (colOrder j).val ≠ 8 ∧ (colOrder j).val ≠ 9 ∧ (colOrder j).val ≠ 10 := by decide
  simp only [literalRow132, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat20_lower_zero

theorem rowFlat21_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨21,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨21,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨10,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row134]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨21,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 9 ∧ (colOrder j).val ≠ 10 := by decide
  simp only [literalRow134, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat21_lower_zero

theorem rowFlat22_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨22,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨22,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨11,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row136]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨22,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 9 ∧ (colOrder j).val ≠ 10 ∧ (colOrder j).val ≠ 11 ∧ (colOrder j).val ≠ 12 ∧ (colOrder j).val ≠ 13 ∧ (colOrder j).val ≠ 14 := by decide
  simp only [literalRow136, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2]

#print axioms rowFlat22_lower_zero

theorem rowFlat23_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨23,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨23,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨12,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row138]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨23,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 11 ∧ (colOrder j).val ≠ 12 := by decide
  simp only [literalRow138, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat23_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk03

import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk07

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk08
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk07

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat16_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨16,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨16,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨29,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row172]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨16,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 27 ∧ (colOrder j).val ≠ 28 ∧ (colOrder j).val ≠ 29 ∧ (colOrder j).val ≠ 30 := by decide
  simp only [literalRow172, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat16_lower_zero

theorem rowFlat17_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨17,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨17,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨30,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row174]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨17,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 29 ∧ (colOrder j).val ≠ 30 := by decide
  simp only [literalRow174, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat17_lower_zero

theorem rowFlat7_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨7,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨7,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨31,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row176]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨7,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 29 ∧ (colOrder j).val ≠ 30 ∧ (colOrder j).val ≠ 31 ∧ (colOrder j).val ≠ 32 ∧ (colOrder j).val ≠ 33 ∧ (colOrder j).val ≠ 35 := by decide
  simp only [literalRow176, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2]

#print axioms rowFlat7_lower_zero

theorem rowFlat8_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨8,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨8,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨32,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row178]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨8,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 31 ∧ (colOrder j).val ≠ 32 ∧ (colOrder j).val ≠ 221 := by decide
  simp only [literalRow178, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat8_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk08

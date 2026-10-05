import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk51

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk52
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk51

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat203_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨203,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨203,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨205,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row1004]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨203,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 203 ∧ (colOrder j).val ≠ 204 ∧ (colOrder j).val ≠ 205 ∧ (colOrder j).val ≠ 206 := by decide
  simp only [literalRow1004, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat203_lower_zero

theorem rowFlat204_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨204,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨204,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨206,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row1006]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨204,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 205 ∧ (colOrder j).val ≠ 206 := by decide
  simp only [literalRow1006, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat204_lower_zero

theorem rowFlat193_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨193,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨193,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨207,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row1008]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨193,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 205 ∧ (colOrder j).val ≠ 206 ∧ (colOrder j).val ≠ 207 ∧ (colOrder j).val ≠ 208 ∧ (colOrder j).val ≠ 209 := by decide
  simp only [literalRow1008, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2]

#print axioms rowFlat193_lower_zero

theorem rowFlat194_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨194,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨194,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨208,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row1011]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨194,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 207 ∧ (colOrder j).val ≠ 208 := by decide
  simp only [literalRow1011, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat194_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk52

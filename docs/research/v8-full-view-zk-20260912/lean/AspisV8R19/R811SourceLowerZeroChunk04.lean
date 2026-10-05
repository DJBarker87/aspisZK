import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk03

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk04
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk03

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat24_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨24,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨24,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨13,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row140]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨24,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 11 ∧ (colOrder j).val ≠ 12 ∧ (colOrder j).val ≠ 13 ∧ (colOrder j).val ≠ 14 := by decide
  simp only [literalRow140, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat24_lower_zero

theorem rowFlat25_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨25,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨25,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨14,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row142]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨25,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 13 ∧ (colOrder j).val ≠ 14 := by decide
  simp only [literalRow142, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat25_lower_zero

theorem rowFlat26_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨26,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨26,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨15,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row144]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨26,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 13 ∧ (colOrder j).val ≠ 14 ∧ (colOrder j).val ≠ 15 ∧ (colOrder j).val ≠ 16 ∧ (colOrder j).val ≠ 17 ∧ (colOrder j).val ≠ 18 ∧ (colOrder j).val ≠ 21 ∧ (colOrder j).val ≠ 22 := by decide
  simp only [literalRow144, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2.2]

#print axioms rowFlat26_lower_zero

theorem rowFlat27_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨27,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨27,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨16,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row146]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨27,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 15 ∧ (colOrder j).val ≠ 16 := by decide
  simp only [literalRow146, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat27_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk04

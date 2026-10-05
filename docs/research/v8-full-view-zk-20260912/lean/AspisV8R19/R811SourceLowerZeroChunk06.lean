import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk05

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk06
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk05

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat32_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨32,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨32,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨21,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row156]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨32,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 19 ∧ (colOrder j).val ≠ 20 ∧ (colOrder j).val ≠ 21 ∧ (colOrder j).val ≠ 22 := by decide
  simp only [literalRow156, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat32_lower_zero

theorem rowFlat33_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨33,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨33,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨22,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row158]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨33,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 21 ∧ (colOrder j).val ≠ 22 := by decide
  simp only [literalRow158, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat33_lower_zero

theorem rowFlat10_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨10,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨10,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨23,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row160]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨10,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 21 ∧ (colOrder j).val ≠ 22 ∧ (colOrder j).val ≠ 23 ∧ (colOrder j).val ≠ 24 ∧ (colOrder j).val ≠ 25 ∧ (colOrder j).val ≠ 26 ∧ (colOrder j).val ≠ 29 ∧ (colOrder j).val ≠ 30 ∧ (colOrder j).val ≠ 35 := by decide
  simp only [literalRow160, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2.2.2]

#print axioms rowFlat10_lower_zero

theorem rowFlat11_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨11,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨11,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨24,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row162]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨11,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 23 ∧ (colOrder j).val ≠ 24 ∧ (colOrder j).val ≠ 221 := by decide
  simp only [literalRow162, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat11_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk06

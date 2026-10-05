import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk33

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk34
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk33

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat138_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨138,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨138,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨133,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row511]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨138,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 132 ∧ (colOrder j).val ≠ 133 := by decide
  simp only [literalRow511, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat138_lower_zero

theorem rowFlat142_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨142,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨142,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨134,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row626]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨142,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 134 ∧ (colOrder j).val ≠ 141 := by decide
  simp only [literalRow626, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat142_lower_zero

theorem rowFlat143_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨143,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨143,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨135,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row628]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨143,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 134 ∧ (colOrder j).val ≠ 135 ∧ (colOrder j).val ≠ 136 := by decide
  simp only [literalRow628, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat143_lower_zero

theorem rowFlat144_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨144,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨144,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨136,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row630]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨144,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 135 ∧ (colOrder j).val ≠ 136 := by decide
  simp only [literalRow630, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat144_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk34

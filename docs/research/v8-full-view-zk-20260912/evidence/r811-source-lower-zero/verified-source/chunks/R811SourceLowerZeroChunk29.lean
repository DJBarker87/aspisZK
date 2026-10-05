import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk28

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk29
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk28

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat101_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨101,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨101,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨113,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row353]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨101,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 112 ∧ (colOrder j).val ≠ 113 ∧ (colOrder j).val ≠ 114 ∧ (colOrder j).val ≠ 116 ∧ (colOrder j).val ≠ 119 := by decide
  simp only [literalRow353, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2]

#print axioms rowFlat101_lower_zero

theorem rowFlat102_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨102,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨102,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨114,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row355]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨102,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 113 ∧ (colOrder j).val ≠ 114 := by decide
  simp only [literalRow355, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat102_lower_zero

theorem rowFlat103_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨103,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨103,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨115,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row357]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨103,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 114 ∧ (colOrder j).val ≠ 115 ∧ (colOrder j).val ≠ 116 := by decide
  simp only [literalRow357, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat103_lower_zero

theorem rowFlat104_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨104,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨104,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨116,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row359]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨104,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 115 ∧ (colOrder j).val ≠ 116 := by decide
  simp only [literalRow359, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat104_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk29

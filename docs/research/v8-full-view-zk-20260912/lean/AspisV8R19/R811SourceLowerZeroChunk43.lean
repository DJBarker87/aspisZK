import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk42

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk43
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk42

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat183_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨183,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨183,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨169,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row926]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨183,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 168 ∧ (colOrder j).val ≠ 169 := by decide
  simp only [literalRow926, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat183_lower_zero

theorem rowFlat168_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨168,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨168,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨170,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row928]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨168,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 168 ∧ (colOrder j).val ≠ 169 ∧ (colOrder j).val ≠ 170 ∧ (colOrder j).val ≠ 171 ∧ (colOrder j).val ≠ 172 ∧ (colOrder j).val ≠ 173 ∧ (colOrder j).val ≠ 176 ∧ (colOrder j).val ≠ 177 ∧ (colOrder j).val ≠ 182 := by decide
  simp only [literalRow928, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2.2.2]

#print axioms rowFlat168_lower_zero

theorem rowFlat169_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨169,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨169,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨171,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row930]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨169,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 170 ∧ (colOrder j).val ≠ 171 := by decide
  simp only [literalRow930, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat169_lower_zero

theorem rowFlat170_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨170,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨170,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨172,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row932]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨170,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 170 ∧ (colOrder j).val ≠ 171 ∧ (colOrder j).val ≠ 172 ∧ (colOrder j).val ≠ 173 := by decide
  simp only [literalRow932, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat170_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk43

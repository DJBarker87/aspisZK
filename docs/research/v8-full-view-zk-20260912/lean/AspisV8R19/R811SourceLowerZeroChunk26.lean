import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk25

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk26
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk25

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat109_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨109,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨109,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨101,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row329]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨109,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 100 ∧ (colOrder j).val ≠ 101 ∧ (colOrder j).val ≠ 102 ∧ (colOrder j).val ≠ 104 := by decide
  simp only [literalRow329, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat109_lower_zero

theorem rowFlat110_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨110,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨110,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨102,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row331]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨110,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 101 ∧ (colOrder j).val ≠ 102 := by decide
  simp only [literalRow331, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat110_lower_zero

theorem rowFlat111_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨111,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨111,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨103,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row333]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨111,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 102 ∧ (colOrder j).val ≠ 103 ∧ (colOrder j).val ≠ 104 := by decide
  simp only [literalRow333, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat111_lower_zero

theorem rowFlat112_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨112,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨112,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨104,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row335]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨112,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 103 ∧ (colOrder j).val ≠ 104 := by decide
  simp only [literalRow335, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat112_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk26

import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk13

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk14
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk13

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat59_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨59,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨59,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨53,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row228]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨59,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 51 ∧ (colOrder j).val ≠ 52 ∧ (colOrder j).val ≠ 53 ∧ (colOrder j).val ≠ 54 := by decide
  simp only [literalRow228, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat59_lower_zero

theorem rowFlat60_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨60,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨60,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨54,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row230]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨60,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 53 ∧ (colOrder j).val ≠ 54 := by decide
  simp only [literalRow230, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat60_lower_zero

theorem rowFlat61_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨61,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨61,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨55,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row232]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨61,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 53 ∧ (colOrder j).val ≠ 54 ∧ (colOrder j).val ≠ 55 ∧ (colOrder j).val ≠ 56 ∧ (colOrder j).val ≠ 57 ∧ (colOrder j).val ≠ 58 := by decide
  simp only [literalRow232, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2]

#print axioms rowFlat61_lower_zero

theorem rowFlat62_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨62,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨62,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨56,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row234]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨62,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 55 ∧ (colOrder j).val ≠ 56 := by decide
  simp only [literalRow234, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat62_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk14

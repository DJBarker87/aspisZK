import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk00

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk01
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk00

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat36_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨36,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨36,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨1,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row116]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨36,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 0 ∧ (colOrder j).val ≠ 1 ∧ (colOrder j).val ≠ 2 := by decide
  simp only [literalRow116, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1]

#print axioms rowFlat36_lower_zero

theorem rowFlat37_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨37,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨37,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨2,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row118]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨37,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 1 ∧ (colOrder j).val ≠ 2 := by decide
  simp only [literalRow118, if_neg (excluded j h).1, if_neg (excluded j h).2.1]

#print axioms rowFlat37_lower_zero

theorem rowFlat38_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨38,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨38,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨3,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row120]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨38,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 1 ∧ (colOrder j).val ≠ 2 ∧ (colOrder j).val ≠ 3 ∧ (colOrder j).val ≠ 4 ∧ (colOrder j).val ≠ 5 ∧ (colOrder j).val ≠ 6 := by decide
  simp only [literalRow120, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.1]

#print axioms rowFlat38_lower_zero

theorem rowFlat39_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨39,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨39,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨4,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row122]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨39,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 3 ∧ (colOrder j).val ≠ 4 := by decide
  simp only [literalRow122, if_neg (excluded j h).1, if_neg (excluded j h).2.1]

#print axioms rowFlat39_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk01

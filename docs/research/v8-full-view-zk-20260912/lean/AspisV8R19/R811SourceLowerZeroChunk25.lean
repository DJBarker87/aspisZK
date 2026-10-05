import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk24

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk25
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk24

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat105_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨105,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨105,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨97,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row321]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨105,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 96 ∧ (colOrder j).val ≠ 97 ∧ (colOrder j).val ≠ 98 ∧ (colOrder j).val ≠ 100 ∧ (colOrder j).val ≠ 104 ∧ (colOrder j).val ≠ 112 := by decide
  simp only [literalRow321, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2]

#print axioms rowFlat105_lower_zero

theorem rowFlat106_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨106,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨106,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨98,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row323]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨106,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 97 ∧ (colOrder j).val ≠ 98 := by decide
  simp only [literalRow323, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat106_lower_zero

theorem rowFlat107_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨107,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨107,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨99,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row325]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨107,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 98 ∧ (colOrder j).val ≠ 99 ∧ (colOrder j).val ≠ 100 := by decide
  simp only [literalRow325, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat107_lower_zero

theorem rowFlat108_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨108,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨108,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨100,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row327]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨108,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 99 ∧ (colOrder j).val ≠ 100 := by decide
  simp only [literalRow327, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat108_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk25

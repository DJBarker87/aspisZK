import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk14

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk15
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk14

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat63_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨63,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨63,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨57,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row236]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨63,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 55 ∧ (colOrder j).val ≠ 56 ∧ (colOrder j).val ≠ 57 ∧ (colOrder j).val ≠ 58 := by decide
  simp only [literalRow236, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat63_lower_zero

theorem rowFlat64_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨64,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨64,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨58,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row238]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨64,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 57 ∧ (colOrder j).val ≠ 58 := by decide
  simp only [literalRow238, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat64_lower_zero

theorem rowFlat65_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨65,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨65,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨59,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row240]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨65,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 57 ∧ (colOrder j).val ≠ 58 ∧ (colOrder j).val ≠ 59 ∧ (colOrder j).val ≠ 60 ∧ (colOrder j).val ≠ 61 ∧ (colOrder j).val ≠ 65 := by decide
  simp only [literalRow240, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2]

#print axioms rowFlat65_lower_zero

theorem rowFlat66_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨66,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨66,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨60,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row243]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨66,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 59 ∧ (colOrder j).val ≠ 60 := by decide
  simp only [literalRow243, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat66_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk15

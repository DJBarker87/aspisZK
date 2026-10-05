import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk08

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk09
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk08

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat9_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨9,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨9,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨33,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row180]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨9,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 31 ∧ (colOrder j).val ≠ 32 ∧ (colOrder j).val ≠ 33 := by decide
  simp only [literalRow180, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat9_lower_zero

theorem rowFlat6_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨6,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨6,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨34,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row184]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨6,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 33 ∧ (colOrder j).val ≠ 34 ∧ (colOrder j).val ≠ 35 := by decide
  simp only [literalRow184, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat6_lower_zero

theorem rowFlat34_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨34,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨34,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨35,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row190]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨34,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 35 ∧ (colOrder j).val ≠ 221 := by decide
  simp only [literalRow190, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat34_lower_zero

theorem rowFlat42_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨42,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨42,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨36,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row194]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨42,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 36 ∧ (colOrder j).val ≠ 221 := by decide
  simp only [literalRow194, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat42_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk09

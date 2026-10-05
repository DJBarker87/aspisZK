import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk29

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk30
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk29

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat100_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨100,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨100,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨117,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row361]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨100,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 116 ∧ (colOrder j).val ≠ 117 ∧ (colOrder j).val ≠ 119 := by decide
  simp only [literalRow361, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat100_lower_zero

theorem rowFlat133_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨133,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨133,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨118,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row365]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨133,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 118 ∧ (colOrder j).val ≠ 119 := by decide
  simp only [literalRow365, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat133_lower_zero

theorem rowFlat134_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨134,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨134,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨119,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row367]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨134,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 118 ∧ (colOrder j).val ≠ 119 := by decide
  simp only [literalRow367, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat134_lower_zero

theorem rowFlat132_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨132,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨132,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨120,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row370]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨132,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 119 ∧ (colOrder j).val ≠ 120 := by decide
  simp only [literalRow370, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat132_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk30

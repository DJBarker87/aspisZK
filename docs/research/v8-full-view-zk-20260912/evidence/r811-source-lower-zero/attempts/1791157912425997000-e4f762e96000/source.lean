import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk31

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk32
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk31

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat128_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨128,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨128,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨125,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row380]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨128,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 123 ∧ (colOrder j).val ≠ 124 ∧ (colOrder j).val ≠ 125 ∧ (colOrder j).val ≠ 126 := by decide
  simp only [literalRow380, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat128_lower_zero

theorem rowFlat129_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨129,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨129,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨126,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row382]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨129,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 125 ∧ (colOrder j).val ≠ 126 := by decide
  simp only [literalRow382, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat129_lower_zero

theorem rowFlat141_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨141,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨141,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨127,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row499]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨141,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 127 := by decide
  simp only [literalRow499, if_neg (excluded j h)]

#print axioms rowFlat141_lower_zero

theorem rowFlat139_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨139,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨139,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨128,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row501]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨139,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 127 ∧ (colOrder j).val ≠ 128 ∧ (colOrder j).val ≠ 129 := by decide
  simp only [literalRow501, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat139_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk32

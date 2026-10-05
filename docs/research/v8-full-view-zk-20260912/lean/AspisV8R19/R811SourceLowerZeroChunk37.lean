import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk36

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk37
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk36

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat152_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨152,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨152,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨145,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row761]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨152,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 144 ∧ (colOrder j).val ≠ 145 ∧ (colOrder j).val ≠ 146 := by decide
  simp only [literalRow761, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat152_lower_zero

theorem rowFlat153_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨153,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨153,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨146,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row763]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨153,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 145 ∧ (colOrder j).val ≠ 146 := by decide
  simp only [literalRow763, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat153_lower_zero

theorem rowFlat150_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨150,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨150,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨147,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row765]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨150,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 146 ∧ (colOrder j).val ≠ 147 ∧ (colOrder j).val ≠ 148 := by decide
  simp only [literalRow765, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat150_lower_zero

theorem rowFlat151_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨151,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨151,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨148,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row766]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨151,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 146 ∧ (colOrder j).val ≠ 147 ∧ (colOrder j).val ≠ 148 := by decide
  simp only [literalRow766, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat151_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk37

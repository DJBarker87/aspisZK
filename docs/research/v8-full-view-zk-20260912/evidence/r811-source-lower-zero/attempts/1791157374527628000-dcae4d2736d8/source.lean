import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk11

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk12
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk11

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat51_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨51,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨51,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨45,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row212]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨51,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 43 ∧ (colOrder j).val ≠ 44 ∧ (colOrder j).val ≠ 45 ∧ (colOrder j).val ≠ 46 := by decide
  simp only [literalRow212, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat51_lower_zero

theorem rowFlat52_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨52,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨52,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨46,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row214]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨52,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 45 ∧ (colOrder j).val ≠ 46 := by decide
  simp only [literalRow214, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat52_lower_zero

theorem rowFlat53_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨53,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨53,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨47,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row216]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨53,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 45 ∧ (colOrder j).val ≠ 46 ∧ (colOrder j).val ≠ 47 ∧ (colOrder j).val ≠ 48 ∧ (colOrder j).val ≠ 49 ∧ (colOrder j).val ≠ 50 := by decide
  simp only [literalRow216, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2]

#print axioms rowFlat53_lower_zero

theorem rowFlat54_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨54,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨54,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨48,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row218]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨54,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 47 ∧ (colOrder j).val ≠ 48 := by decide
  simp only [literalRow218, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat54_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk12

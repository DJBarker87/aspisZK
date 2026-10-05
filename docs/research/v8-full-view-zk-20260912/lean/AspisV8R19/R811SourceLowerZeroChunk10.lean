import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk09

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk10
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk09

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat43_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨43,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨43,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨37,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row196]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨43,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 36 ∧ (colOrder j).val ≠ 37 ∧ (colOrder j).val ≠ 38 := by decide
  simp only [literalRow196, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat43_lower_zero

theorem rowFlat44_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨44,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨44,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨38,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row198]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨44,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 37 ∧ (colOrder j).val ≠ 38 := by decide
  simp only [literalRow198, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat44_lower_zero

theorem rowFlat45_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨45,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨45,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨39,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row200]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨45,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 37 ∧ (colOrder j).val ≠ 38 ∧ (colOrder j).val ≠ 39 ∧ (colOrder j).val ≠ 40 ∧ (colOrder j).val ≠ 41 ∧ (colOrder j).val ≠ 42 := by decide
  simp only [literalRow200, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2]

#print axioms rowFlat45_lower_zero

theorem rowFlat46_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨46,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨46,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨40,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row202]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨46,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 39 ∧ (colOrder j).val ≠ 40 := by decide
  simp only [literalRow202, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat46_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk10

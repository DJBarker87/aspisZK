import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk43

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk44
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk43

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat171_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨171,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨171,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨173,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row934]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨171,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 172 ∧ (colOrder j).val ≠ 173 := by decide
  simp only [literalRow934, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat171_lower_zero

theorem rowFlat172_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨172,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨172,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨174,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row936]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨172,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 172 ∧ (colOrder j).val ≠ 173 ∧ (colOrder j).val ≠ 174 ∧ (colOrder j).val ≠ 175 ∧ (colOrder j).val ≠ 176 ∧ (colOrder j).val ≠ 177 := by decide
  simp only [literalRow936, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2]

#print axioms rowFlat172_lower_zero

theorem rowFlat173_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨173,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨173,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨175,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row938]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨173,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 174 ∧ (colOrder j).val ≠ 175 := by decide
  simp only [literalRow938, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat173_lower_zero

theorem rowFlat174_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨174,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨174,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨176,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row940]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨174,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 174 ∧ (colOrder j).val ≠ 175 ∧ (colOrder j).val ≠ 176 ∧ (colOrder j).val ≠ 177 := by decide
  simp only [literalRow940, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat174_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk44

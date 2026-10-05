import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk46

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk47
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk46

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat207_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨207,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨207,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨185,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row964]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨207,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 183 ∧ (colOrder j).val ≠ 184 ∧ (colOrder j).val ≠ 185 ∧ (colOrder j).val ≠ 186 := by decide
  simp only [literalRow964, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat207_lower_zero

theorem rowFlat208_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨208,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨208,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨186,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row966]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨208,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 185 ∧ (colOrder j).val ≠ 186 := by decide
  simp only [literalRow966, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat208_lower_zero

theorem rowFlat209_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨209,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨209,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨187,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row968]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨209,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 185 ∧ (colOrder j).val ≠ 186 ∧ (colOrder j).val ≠ 187 ∧ (colOrder j).val ≠ 188 ∧ (colOrder j).val ≠ 189 ∧ (colOrder j).val ≠ 190 := by decide
  simp only [literalRow968, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2]

#print axioms rowFlat209_lower_zero

theorem rowFlat210_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨210,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨210,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨188,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row970]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨210,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 187 ∧ (colOrder j).val ≠ 188 := by decide
  simp only [literalRow970, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat210_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk47

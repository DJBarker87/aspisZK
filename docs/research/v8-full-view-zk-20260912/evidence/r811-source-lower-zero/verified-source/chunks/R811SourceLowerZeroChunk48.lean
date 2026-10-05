import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk47

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk48
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk47

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat211_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨211,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨211,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨189,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row972]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨211,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 187 ∧ (colOrder j).val ≠ 188 ∧ (colOrder j).val ≠ 189 ∧ (colOrder j).val ≠ 190 := by decide
  simp only [literalRow972, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat211_lower_zero

theorem rowFlat212_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨212,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨212,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨190,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row974]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨212,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 189 ∧ (colOrder j).val ≠ 190 := by decide
  simp only [literalRow974, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat212_lower_zero

theorem rowFlat213_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨213,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨213,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨191,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row976]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨213,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 189 ∧ (colOrder j).val ≠ 190 ∧ (colOrder j).val ≠ 191 ∧ (colOrder j).val ≠ 192 ∧ (colOrder j).val ≠ 193 ∧ (colOrder j).val ≠ 194 ∧ (colOrder j).val ≠ 197 ∧ (colOrder j).val ≠ 198 := by decide
  simp only [literalRow976, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2.2]

#print axioms rowFlat213_lower_zero

theorem rowFlat214_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨214,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨214,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨192,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row978]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨214,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 191 ∧ (colOrder j).val ≠ 192 := by decide
  simp only [literalRow978, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat214_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk48

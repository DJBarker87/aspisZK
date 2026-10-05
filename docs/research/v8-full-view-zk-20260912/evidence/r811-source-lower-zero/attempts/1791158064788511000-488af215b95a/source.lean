import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk40

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk41
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk40

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat187_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨187,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨187,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨161,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row910]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨187,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 160 ∧ (colOrder j).val ≠ 161 := by decide
  simp only [literalRow910, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat187_lower_zero

theorem rowFlat176_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨176,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨176,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨162,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row912]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨176,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 160 ∧ (colOrder j).val ≠ 161 ∧ (colOrder j).val ≠ 162 ∧ (colOrder j).val ≠ 163 ∧ (colOrder j).val ≠ 164 ∧ (colOrder j).val ≠ 165 ∧ (colOrder j).val ≠ 168 ∧ (colOrder j).val ≠ 169 := by decide
  simp only [literalRow912, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2.2]

#print axioms rowFlat176_lower_zero

theorem rowFlat177_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨177,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨177,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨163,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row914]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨177,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 162 ∧ (colOrder j).val ≠ 163 := by decide
  simp only [literalRow914, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat177_lower_zero

theorem rowFlat178_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨178,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨178,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨164,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row916]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨178,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 162 ∧ (colOrder j).val ≠ 163 ∧ (colOrder j).val ≠ 164 ∧ (colOrder j).val ≠ 165 := by decide
  simp only [literalRow916, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat178_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk41

import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk48

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk49
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk48

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat215_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨215,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨215,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨193,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row980]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨215,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 191 ∧ (colOrder j).val ≠ 192 ∧ (colOrder j).val ≠ 193 ∧ (colOrder j).val ≠ 194 := by decide
  simp only [literalRow980, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat215_lower_zero

theorem rowFlat216_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨216,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨216,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨194,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row982]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨216,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 193 ∧ (colOrder j).val ≠ 194 := by decide
  simp only [literalRow982, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat216_lower_zero

theorem rowFlat217_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨217,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨217,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨195,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row984]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨217,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 193 ∧ (colOrder j).val ≠ 194 ∧ (colOrder j).val ≠ 195 ∧ (colOrder j).val ≠ 196 ∧ (colOrder j).val ≠ 197 ∧ (colOrder j).val ≠ 198 := by decide
  simp only [literalRow984, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2]

#print axioms rowFlat217_lower_zero

theorem rowFlat218_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨218,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨218,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨196,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row986]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨218,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 195 ∧ (colOrder j).val ≠ 196 := by decide
  simp only [literalRow986, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat218_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk49

import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk17

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk18
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk17

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat87_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨87,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨87,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨69,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row263]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨87,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 68 ∧ (colOrder j).val ≠ 69 := by decide
  simp only [literalRow263, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat87_lower_zero

theorem rowFlat88_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨88,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨88,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨70,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row265]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨88,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 69 ∧ (colOrder j).val ≠ 70 ∧ (colOrder j).val ≠ 71 ∧ (colOrder j).val ≠ 73 := by decide
  simp only [literalRow265, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat88_lower_zero

theorem rowFlat89_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨89,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨89,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨71,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row267]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨89,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 70 ∧ (colOrder j).val ≠ 71 := by decide
  simp only [literalRow267, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat89_lower_zero

theorem rowFlat90_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨90,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨90,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨72,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row269]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨90,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 71 ∧ (colOrder j).val ≠ 72 ∧ (colOrder j).val ≠ 73 := by decide
  simp only [literalRow269, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat90_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk18

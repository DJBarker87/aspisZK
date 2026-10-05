import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk22

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk23
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk22

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat83_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨83,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨83,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨89,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row303]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨83,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 88 ∧ (colOrder j).val ≠ 89 := by decide
  simp only [literalRow303, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat83_lower_zero

theorem rowFlat74_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨74,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨74,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨90,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row305]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨74,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 89 ∧ (colOrder j).val ≠ 90 ∧ (colOrder j).val ≠ 91 ∧ (colOrder j).val ≠ 92 ∧ (colOrder j).val ≠ 96 := by decide
  simp only [literalRow305, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2]

#print axioms rowFlat74_lower_zero

theorem rowFlat75_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨75,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨75,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨91,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row307]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨75,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 90 ∧ (colOrder j).val ≠ 91 := by decide
  simp only [literalRow307, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat75_lower_zero

theorem rowFlat125_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨125,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨125,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨92,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row311]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨125,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 92 := by decide
  simp only [literalRow311, if_neg (excluded j h)]

#print axioms rowFlat125_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk23

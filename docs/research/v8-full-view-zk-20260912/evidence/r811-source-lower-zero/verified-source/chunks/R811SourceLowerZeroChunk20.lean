import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk19

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk20
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk19

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat95_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨95,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨95,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨77,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row279]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨95,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 76 ∧ (colOrder j).val ≠ 77 := by decide
  simp only [literalRow279, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat95_lower_zero

theorem rowFlat96_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨96,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨96,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨78,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row281]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨96,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 77 ∧ (colOrder j).val ≠ 78 ∧ (colOrder j).val ≠ 79 ∧ (colOrder j).val ≠ 81 := by decide
  simp only [literalRow281, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat96_lower_zero

theorem rowFlat97_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨97,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨97,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨79,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row283]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨97,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 78 ∧ (colOrder j).val ≠ 79 := by decide
  simp only [literalRow283, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat97_lower_zero

theorem rowFlat98_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨98,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨98,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨80,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row285]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨98,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 79 ∧ (colOrder j).val ≠ 80 ∧ (colOrder j).val ≠ 81 := by decide
  simp only [literalRow285, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat98_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk20

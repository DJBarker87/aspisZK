import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk35

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk36
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk35

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat149_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨149,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨149,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨141,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row639]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨149,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 139 ∧ (colOrder j).val ≠ 140 ∧ (colOrder j).val ≠ 141 := by decide
  simp only [literalRow639, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat149_lower_zero

theorem rowFlat156_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨156,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨156,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨142,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row755]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨156,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 142 := by decide
  simp only [literalRow755, if_neg (excluded j h)]

#print axioms rowFlat156_lower_zero

theorem rowFlat154_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨154,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨154,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨143,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row757]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨154,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 142 ∧ (colOrder j).val ≠ 143 ∧ (colOrder j).val ≠ 144 := by decide
  simp only [literalRow757, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat154_lower_zero

theorem rowFlat155_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨155,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨155,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨144,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row759]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨155,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 143 ∧ (colOrder j).val ≠ 144 := by decide
  simp only [literalRow759, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat155_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk36

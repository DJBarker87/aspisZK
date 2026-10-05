import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk45

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk46
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk45

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat165_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨165,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨165,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨181,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row954]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨165,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 180 ∧ (colOrder j).val ≠ 181 := by decide
  simp only [literalRow954, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat165_lower_zero

theorem rowFlat221_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨221,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨221,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨182,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row958]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨221,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 182 := by decide
  simp only [literalRow958, if_neg (excluded j h)]

#print axioms rowFlat221_lower_zero

theorem rowFlat205_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨205,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨205,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨183,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row960]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨205,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 182 ∧ (colOrder j).val ≠ 183 ∧ (colOrder j).val ≠ 184 ∧ (colOrder j).val ≠ 185 ∧ (colOrder j).val ≠ 186 ∧ (colOrder j).val ≠ 189 ∧ (colOrder j).val ≠ 190 ∧ (colOrder j).val ≠ 197 ∧ (colOrder j).val ≠ 198 := by decide
  simp only [literalRow960, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2.2.2]

#print axioms rowFlat205_lower_zero

theorem rowFlat206_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨206,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨206,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨184,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row962]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨206,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 183 ∧ (colOrder j).val ≠ 184 := by decide
  simp only [literalRow962, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat206_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk46

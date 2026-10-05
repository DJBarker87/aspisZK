import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk15

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk16
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk15

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat67_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨67,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨67,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨61,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row245]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨67,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 60 ∧ (colOrder j).val ≠ 61 ∧ (colOrder j).val ≠ 62 := by decide
  simp only [literalRow245, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat67_lower_zero

theorem rowFlat68_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨68,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨68,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨62,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row247]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨68,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 61 ∧ (colOrder j).val ≠ 62 := by decide
  simp only [literalRow247, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat68_lower_zero

theorem rowFlat69_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨69,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨69,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨63,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row249]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨69,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 62 ∧ (colOrder j).val ≠ 63 ∧ (colOrder j).val ≠ 64 := by decide
  simp only [literalRow249, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat69_lower_zero

theorem rowFlat70_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨70,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨70,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨64,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row251]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨70,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 63 ∧ (colOrder j).val ≠ 64 := by decide
  simp only [literalRow251, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat70_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk16

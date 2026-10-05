import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk23

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk24
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk23

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat121_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨121,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨121,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨93,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row313]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨121,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 92 ∧ (colOrder j).val ≠ 93 ∧ (colOrder j).val ≠ 94 ∧ (colOrder j).val ≠ 96 := by decide
  simp only [literalRow313, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat121_lower_zero

theorem rowFlat122_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨122,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨122,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨94,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row315]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨122,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 93 ∧ (colOrder j).val ≠ 94 := by decide
  simp only [literalRow315, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat122_lower_zero

theorem rowFlat123_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨123,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨123,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨95,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row317]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨123,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 94 ∧ (colOrder j).val ≠ 95 ∧ (colOrder j).val ≠ 96 := by decide
  simp only [literalRow317, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat123_lower_zero

theorem rowFlat124_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨124,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨124,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨96,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row319]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨124,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 95 ∧ (colOrder j).val ≠ 96 := by decide
  simp only [literalRow319, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat124_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk24

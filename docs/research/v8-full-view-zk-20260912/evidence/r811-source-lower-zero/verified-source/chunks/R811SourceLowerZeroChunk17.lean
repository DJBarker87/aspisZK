import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk16

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk17
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk16

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat71_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨71,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨71,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨65,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row253]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨71,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 64 ∧ (colOrder j).val ≠ 65 := by decide
  simp only [literalRow253, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat71_lower_zero

theorem rowFlat84_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨84,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨84,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨66,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row257]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨84,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 66 ∧ (colOrder j).val ≠ 67 ∧ (colOrder j).val ≠ 69 ∧ (colOrder j).val ≠ 73 ∧ (colOrder j).val ≠ 81 ∧ (colOrder j).val ≠ 96 ∧ (colOrder j).val ≠ 133 := by decide
  simp only [literalRow257, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2]

#print axioms rowFlat84_lower_zero

theorem rowFlat85_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨85,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨85,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨67,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row259]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨85,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 66 ∧ (colOrder j).val ≠ 67 := by decide
  simp only [literalRow259, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat85_lower_zero

theorem rowFlat86_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨86,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨86,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨68,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row261]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨86,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 67 ∧ (colOrder j).val ≠ 68 ∧ (colOrder j).val ≠ 69 := by decide
  simp only [literalRow261, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat86_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk17

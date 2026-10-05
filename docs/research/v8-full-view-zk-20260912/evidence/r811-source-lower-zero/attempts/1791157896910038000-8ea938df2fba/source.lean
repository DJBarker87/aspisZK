import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk30

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk31
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk30

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat130_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨130,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨130,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨121,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row372]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨130,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 120 ∧ (colOrder j).val ≠ 121 ∧ (colOrder j).val ≠ 122 := by decide
  simp only [literalRow372, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat130_lower_zero

theorem rowFlat131_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨131,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨131,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨122,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row374]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨131,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 121 ∧ (colOrder j).val ≠ 122 := by decide
  simp only [literalRow374, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat131_lower_zero

theorem rowFlat126_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨126,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨126,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨123,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row376]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨126,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 121 ∧ (colOrder j).val ≠ 122 ∧ (colOrder j).val ≠ 123 ∧ (colOrder j).val ≠ 124 ∧ (colOrder j).val ≠ 125 ∧ (colOrder j).val ≠ 126 := by decide
  simp only [literalRow376, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2]

#print axioms rowFlat126_lower_zero

theorem rowFlat127_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨127,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨127,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨124,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row378]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨127,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 123 ∧ (colOrder j).val ≠ 124 := by decide
  simp only [literalRow378, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat127_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk31

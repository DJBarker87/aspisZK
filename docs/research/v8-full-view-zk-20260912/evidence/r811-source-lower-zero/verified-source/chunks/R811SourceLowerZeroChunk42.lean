import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk41

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk42
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk41

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat179_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨179,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨179,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨165,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row918]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨179,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 164 ∧ (colOrder j).val ≠ 165 := by decide
  simp only [literalRow918, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat179_lower_zero

theorem rowFlat180_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨180,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨180,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨166,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row920]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨180,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 164 ∧ (colOrder j).val ≠ 165 ∧ (colOrder j).val ≠ 166 ∧ (colOrder j).val ≠ 167 ∧ (colOrder j).val ≠ 168 ∧ (colOrder j).val ≠ 169 := by decide
  simp only [literalRow920, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2]

#print axioms rowFlat180_lower_zero

theorem rowFlat181_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨181,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨181,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨167,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row922]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨181,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 166 ∧ (colOrder j).val ≠ 167 := by decide
  simp only [literalRow922, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat181_lower_zero

theorem rowFlat182_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨182,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨182,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨168,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row924]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨182,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 166 ∧ (colOrder j).val ≠ 167 ∧ (colOrder j).val ≠ 168 ∧ (colOrder j).val ≠ 169 := by decide
  simp only [literalRow924, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat182_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk42

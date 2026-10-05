import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk52

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk53
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk52

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat195_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨195,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨195,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨209,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row1013]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨195,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 208 ∧ (colOrder j).val ≠ 209 ∧ (colOrder j).val ≠ 210 := by decide
  simp only [literalRow1013, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat195_lower_zero

theorem rowFlat196_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨196,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨196,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨210,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row1015]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨196,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 209 ∧ (colOrder j).val ≠ 210 := by decide
  simp only [literalRow1015, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat196_lower_zero

theorem rowFlat190_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨190,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨190,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨211,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row1017]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨190,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 210 ∧ (colOrder j).val ≠ 211 ∧ (colOrder j).val ≠ 212 ∧ (colOrder j).val ≠ 213 := by decide
  simp only [literalRow1017, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat190_lower_zero

theorem rowFlat191_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨191,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨191,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨212,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row1019]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨191,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 211 ∧ (colOrder j).val ≠ 212 ∧ (colOrder j).val ≠ 213 := by decide
  simp only [literalRow1019, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat191_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk53

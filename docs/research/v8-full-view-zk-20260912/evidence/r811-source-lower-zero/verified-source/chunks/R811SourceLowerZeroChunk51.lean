import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk50

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk51
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk50

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat199_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨199,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨199,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨201,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row996]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨199,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 199 ∧ (colOrder j).val ≠ 200 ∧ (colOrder j).val ≠ 201 ∧ (colOrder j).val ≠ 202 := by decide
  simp only [literalRow996, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat199_lower_zero

theorem rowFlat200_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨200,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨200,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨202,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row998]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨200,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 201 ∧ (colOrder j).val ≠ 202 := by decide
  simp only [literalRow998, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat200_lower_zero

theorem rowFlat201_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨201,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨201,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨203,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row1000]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨201,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 201 ∧ (colOrder j).val ≠ 202 ∧ (colOrder j).val ≠ 203 ∧ (colOrder j).val ≠ 204 ∧ (colOrder j).val ≠ 205 ∧ (colOrder j).val ≠ 206 := by decide
  simp only [literalRow1000, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2]

#print axioms rowFlat201_lower_zero

theorem rowFlat202_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨202,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨202,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨204,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row1002]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨202,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 203 ∧ (colOrder j).val ≠ 204 := by decide
  simp only [literalRow1002, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat202_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk51

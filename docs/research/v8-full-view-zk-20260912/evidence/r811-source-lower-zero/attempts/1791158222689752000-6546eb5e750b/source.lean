import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk49

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk50
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk49

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat219_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨219,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨219,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨197,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row988]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨219,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 195 ∧ (colOrder j).val ≠ 196 ∧ (colOrder j).val ≠ 197 ∧ (colOrder j).val ≠ 198 := by decide
  simp only [literalRow988, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat219_lower_zero

theorem rowFlat220_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨220,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨220,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨198,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row990]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨220,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 197 ∧ (colOrder j).val ≠ 198 := by decide
  simp only [literalRow990, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat220_lower_zero

theorem rowFlat197_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨197,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨197,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨199,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row992]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨197,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 197 ∧ (colOrder j).val ≠ 198 ∧ (colOrder j).val ≠ 199 ∧ (colOrder j).val ≠ 200 ∧ (colOrder j).val ≠ 201 ∧ (colOrder j).val ≠ 202 ∧ (colOrder j).val ≠ 205 ∧ (colOrder j).val ≠ 206 := by decide
  simp only [literalRow992, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2.2.2]

#print axioms rowFlat197_lower_zero

theorem rowFlat198_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨198,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨198,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨200,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row994]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨198,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 199 ∧ (colOrder j).val ≠ 200 := by decide
  simp only [literalRow994, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat198_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk50

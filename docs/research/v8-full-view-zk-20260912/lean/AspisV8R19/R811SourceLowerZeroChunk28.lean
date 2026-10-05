import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk27

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk28
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk27

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat117_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨117,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨117,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨109,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row345]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨117,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 108 ∧ (colOrder j).val ≠ 109 ∧ (colOrder j).val ≠ 110 ∧ (colOrder j).val ≠ 112 := by decide
  simp only [literalRow345, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat117_lower_zero

theorem rowFlat118_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨118,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨118,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨110,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row347]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨118,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 109 ∧ (colOrder j).val ≠ 110 := by decide
  simp only [literalRow347, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat118_lower_zero

theorem rowFlat119_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨119,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨119,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨111,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row349]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨119,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 110 ∧ (colOrder j).val ≠ 111 ∧ (colOrder j).val ≠ 112 := by decide
  simp only [literalRow349, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat119_lower_zero

theorem rowFlat120_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨120,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨120,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨112,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row351]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨120,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 111 ∧ (colOrder j).val ≠ 112 := by decide
  simp only [literalRow351, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat120_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk28

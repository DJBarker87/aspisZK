import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk04

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk05
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk04

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat28_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨28,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨28,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨17,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row148]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨28,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 15 ∧ (colOrder j).val ≠ 16 ∧ (colOrder j).val ≠ 17 ∧ (colOrder j).val ≠ 18 := by decide
  simp only [literalRow148, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat28_lower_zero

theorem rowFlat29_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨29,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨29,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨18,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row150]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨29,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 17 ∧ (colOrder j).val ≠ 18 := by decide
  simp only [literalRow150, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat29_lower_zero

theorem rowFlat30_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨30,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨30,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨19,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row152]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨30,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 17 ∧ (colOrder j).val ≠ 18 ∧ (colOrder j).val ≠ 19 ∧ (colOrder j).val ≠ 20 ∧ (colOrder j).val ≠ 21 ∧ (colOrder j).val ≠ 22 := by decide
  simp only [literalRow152, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2]

#print axioms rowFlat30_lower_zero

theorem rowFlat31_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨31,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨31,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨20,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row154]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨31,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 19 ∧ (colOrder j).val ≠ 20 := by decide
  simp only [literalRow154, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat31_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk05

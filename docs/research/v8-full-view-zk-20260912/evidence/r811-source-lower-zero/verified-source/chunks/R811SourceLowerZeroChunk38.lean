import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk37

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk38
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk37

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat163_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨163,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨163,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨149,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row882]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨163,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 149 := by decide
  simp only [literalRow882, if_neg (excluded j h)]

#print axioms rowFlat163_lower_zero

theorem rowFlat161_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨161,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨161,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨150,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row884]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨161,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 149 ∧ (colOrder j).val ≠ 150 ∧ (colOrder j).val ≠ 151 := by decide
  simp only [literalRow884, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat161_lower_zero

theorem rowFlat162_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨162,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨162,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨151,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row886]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨162,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 150 ∧ (colOrder j).val ≠ 151 := by decide
  simp only [literalRow886, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat162_lower_zero

theorem rowFlat157_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨157,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨157,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨152,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row888]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨157,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 150 ∧ (colOrder j).val ≠ 151 ∧ (colOrder j).val ≠ 152 ∧ (colOrder j).val ≠ 153 ∧ (colOrder j).val ≠ 154 ∧ (colOrder j).val ≠ 155 := by decide
  simp only [literalRow888, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2]

#print axioms rowFlat157_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk38

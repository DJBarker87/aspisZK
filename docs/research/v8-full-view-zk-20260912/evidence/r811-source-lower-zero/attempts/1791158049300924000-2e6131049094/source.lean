import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk39

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk40
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk39

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat189_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨189,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨189,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨157,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row902]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨189,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 156 ∧ (colOrder j).val ≠ 157 := by decide
  simp only [literalRow902, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat189_lower_zero

theorem rowFlat184_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨184,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨184,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨158,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row904]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨184,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 156 ∧ (colOrder j).val ≠ 157 ∧ (colOrder j).val ≠ 158 ∧ (colOrder j).val ≠ 159 ∧ (colOrder j).val ≠ 160 ∧ (colOrder j).val ≠ 161 := by decide
  simp only [literalRow904, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2]

#print axioms rowFlat184_lower_zero

theorem rowFlat185_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨185,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨185,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨159,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row906]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨185,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 158 ∧ (colOrder j).val ≠ 159 := by decide
  simp only [literalRow906, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat185_lower_zero

theorem rowFlat186_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨186,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨186,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨160,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row908]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨186,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 158 ∧ (colOrder j).val ≠ 159 ∧ (colOrder j).val ≠ 160 ∧ (colOrder j).val ≠ 161 := by decide
  simp only [literalRow908, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat186_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk40

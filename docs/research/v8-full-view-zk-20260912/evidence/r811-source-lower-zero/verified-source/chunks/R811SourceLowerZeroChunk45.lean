import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk44

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk45
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk44

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat175_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨175,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨175,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨177,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row942]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨175,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 176 ∧ (colOrder j).val ≠ 177 := by decide
  simp only [literalRow942, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat175_lower_zero

theorem rowFlat166_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨166,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨166,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨178,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row944]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨166,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 176 ∧ (colOrder j).val ≠ 177 ∧ (colOrder j).val ≠ 178 ∧ (colOrder j).val ≠ 179 ∧ (colOrder j).val ≠ 182 := by decide
  simp only [literalRow944, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2]

#print axioms rowFlat166_lower_zero

theorem rowFlat167_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨167,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨167,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨179,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row948]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨167,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 178 ∧ (colOrder j).val ≠ 179 := by decide
  simp only [literalRow948, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat167_lower_zero

theorem rowFlat164_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨164,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨164,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨180,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row952]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨164,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 179 ∧ (colOrder j).val ≠ 180 ∧ (colOrder j).val ≠ 181 ∧ (colOrder j).val ≠ 182 := by decide
  simp only [literalRow952, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat164_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk45

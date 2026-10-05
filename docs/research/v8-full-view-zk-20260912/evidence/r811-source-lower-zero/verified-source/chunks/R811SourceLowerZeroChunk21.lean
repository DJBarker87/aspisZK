import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk20

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk21
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk20

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat99_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨99,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨99,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨81,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row287]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨99,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 80 ∧ (colOrder j).val ≠ 81 := by decide
  simp only [literalRow287, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat99_lower_zero

theorem rowFlat76_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨76,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨76,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨82,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row289]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨76,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 81 ∧ (colOrder j).val ≠ 82 ∧ (colOrder j).val ≠ 83 ∧ (colOrder j).val ≠ 85 ∧ (colOrder j).val ≠ 89 ∧ (colOrder j).val ≠ 96 := by decide
  simp only [literalRow289, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2.1, if_neg (excluded j h).2.2.2.2.1, if_neg (excluded j h).2.2.2.2.2]

#print axioms rowFlat76_lower_zero

theorem rowFlat77_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨77,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨77,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨83,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row291]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨77,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 82 ∧ (colOrder j).val ≠ 83 := by decide
  simp only [literalRow291, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat77_lower_zero

theorem rowFlat78_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨78,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨78,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨84,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row293]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨78,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 83 ∧ (colOrder j).val ≠ 84 ∧ (colOrder j).val ≠ 85 := by decide
  simp only [literalRow293, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat78_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk21

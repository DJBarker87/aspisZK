import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRowsChunk32

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk33
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk32

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat140_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨140,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨140,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨129,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row503]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨140,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 128 ∧ (colOrder j).val ≠ 129 := by decide
  simp only [literalRow503, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat140_lower_zero

theorem rowFlat135_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨135,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨135,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨130,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row505]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨135,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 129 ∧ (colOrder j).val ≠ 130 ∧ (colOrder j).val ≠ 131 ∧ (colOrder j).val ≠ 133 := by decide
  simp only [literalRow505, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2.1, if_neg (excluded j h).2.2.2]

#print axioms rowFlat135_lower_zero

theorem rowFlat136_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨136,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨136,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨131,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row507]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨136,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 130 ∧ (colOrder j).val ≠ 131 := by decide
  simp only [literalRow507, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat136_lower_zero

theorem rowFlat137_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨137,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨137,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨132,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row509]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨137,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 131 ∧ (colOrder j).val ≠ 132 ∧ (colOrder j).val ≠ 133 := by decide
  simp only [literalRow509, if_neg (excluded j h).1, if_neg (excluded j h).2.1, if_neg (excluded j h).2.2]

#print axioms rowFlat137_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk33

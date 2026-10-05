import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R804LiteralSourceRow1022

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroChunk54
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow1022

noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat192_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨192,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨192,by decide⟩ : Fin 222) j = 0 := by
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨213,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row1022]
  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel (⟨192,by decide⟩ : Fin 222) →
      (colOrder j).val ≠ 212 := by decide
  simp only [literalRow1022, if_neg (excluded j h)]

#print axioms rowFlat192_lower_zero
end
end AspisV8R19.R811SourceLowerZeroChunk54

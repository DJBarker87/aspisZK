import AspisV8R19.R807SourceBlock01Binding

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R811SourceLowerZeroPrototype
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R748JointWitnessPointEntry
noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem rowFlat35_lower_zero (j : Fin 222)
    (h : blockLabel j < blockLabel (⟨35,by decide⟩ : Fin 222)) :
    reorderedSourceMatrix (⟨35,by decide⟩ : Fin 222) j = 0 := by
  change blockLabel j < (6 : Fin 41) at h
  have excluded : ∀ j : Fin 222, blockLabel j < (6 : Fin 41) →
      (colOrder j).val ≠ 0 ∧ (colOrder j).val ≠ 220 := by decide
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨0,by decide⟩ : Fin 214)) (colOrder j) = 0
  rw [literalSourceMatrix_row114]
  simp only [literalRow114, if_neg (excluded j h).1, if_neg (excluded j h).2]

#print axioms rowFlat35_lower_zero
end
end AspisV8R19.R811SourceLowerZeroPrototype

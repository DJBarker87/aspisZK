import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R803LiteralSupplementaryEntries
import AspisV8R19.R806LiteralBlockLayout
import AspisV8R19.R724BlockOrderMaps
import AspisV8R19.R766BlockOrderEquivalences
import AspisV8R19.R816Fin222ActiveSupplementDispatch
import AspisV8R19.R820SupplementaryLowerZero

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R828SupplementarySourceLowerRows
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R803LiteralSupplementaryEntries
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R766BlockOrderEquivalences
open AspisV8R19.R820SupplementaryLowerZero

noncomputable section

def lowerRow (r : Fin 222) : Prop :=
  ∀ ⦃j : Fin 222⦄, blockLabel j < blockLabel (rowOrderInv r) →
    reorderedSourceMatrix (rowOrderInv r) j = 0

theorem supplementary_lowerRow (i : Fin 8) :
    lowerRow (AspisV8R19.R816Fin222ActiveSupplementDispatch.supplementPos i) := by
  fin_cases i
  · intro j hj
    have hflat : rowOrderInv
        (AspisV8R19.R816Fin222ActiveSupplementDispatch.supplementPos (⟨0, by decide⟩ : Fin 8)) =
        (⟨73, by decide⟩ : Fin 222) := by decide
    have hlabel : blockLabel j < (6 : Fin 41) := by
      rw [hflat] at hj
      change blockLabel j < (6 : Fin 41) at hj
      exact hj
    have hz := p0_lower_zero j hlabel
    rw [reorderedSourceMatrix, hflat]
    have hrow : rowOrder (⟨73, by decide⟩ : Fin 222) = pointPosition (⟨0, by decide⟩ : Fin 3) := by decide
    rw [hrow]
    exact hz
  · intro j hj
    have hflat : rowOrderInv
        (AspisV8R19.R816Fin222ActiveSupplementDispatch.supplementPos (⟨1, by decide⟩ : Fin 8)) =
        (⟨0, by decide⟩ : Fin 222) := by decide
    have hbot : blockLabel j < (0 : Fin 41) := by
      rw [hflat] at hj
      change blockLabel j < (0 : Fin 41) at hj
      exact hj
    omega
  · intro j hj
    have hflat : rowOrderInv
        (AspisV8R19.R816Fin222ActiveSupplementDispatch.supplementPos (⟨2, by decide⟩ : Fin 8)) =
        (⟨72, by decide⟩ : Fin 222) := by decide
    have hlabel : blockLabel j < (6 : Fin 41) := by
      rw [hflat] at hj
      change blockLabel j < (6 : Fin 41) at hj
      exact hj
    have hz := p2_lower_zero j hlabel
    rw [reorderedSourceMatrix, hflat]
    have hrow : rowOrder (⟨72, by decide⟩ : Fin 222) = pointPosition (⟨2, by decide⟩ : Fin 3) := by decide
    rw [hrow]
    exact hz
  · intro j hj
    have hflat : rowOrderInv
        (AspisV8R19.R816Fin222ActiveSupplementDispatch.supplementPos (⟨3, by decide⟩ : Fin 8)) =
        (⟨1, by decide⟩ : Fin 222) := by decide
    have hbot : blockLabel j < (0 : Fin 41) := by
      rw [hflat] at hj
      change blockLabel j < (0 : Fin 41) at hj
      exact hj
    omega
  · intro j hj
    have hflat : rowOrderInv
        (AspisV8R19.R816Fin222ActiveSupplementDispatch.supplementPos (⟨4, by decide⟩ : Fin 8)) =
        (⟨2, by decide⟩ : Fin 222) := by decide
    have hbot : blockLabel j < (0 : Fin 41) := by
      rw [hflat] at hj
      change blockLabel j < (0 : Fin 41) at hj
      exact hj
    omega
  · intro j hj
    have hflat : rowOrderInv
        (AspisV8R19.R816Fin222ActiveSupplementDispatch.supplementPos (⟨5, by decide⟩ : Fin 8)) =
        (⟨3, by decide⟩ : Fin 222) := by decide
    have hbot : blockLabel j < (0 : Fin 41) := by
      rw [hflat] at hj
      change blockLabel j < (0 : Fin 41) at hj
      exact hj
    omega
  · intro j hj
    have hflat : rowOrderInv
        (AspisV8R19.R816Fin222ActiveSupplementDispatch.supplementPos (⟨6, by decide⟩ : Fin 8)) =
        (⟨4, by decide⟩ : Fin 222) := by decide
    have hbot : blockLabel j < (0 : Fin 41) := by
      rw [hflat] at hj
      change blockLabel j < (0 : Fin 41) at hj
      exact hj
    omega
  · intro j hj
    have hflat : rowOrderInv
        (AspisV8R19.R816Fin222ActiveSupplementDispatch.supplementPos (⟨7, by decide⟩ : Fin 8)) =
        (⟨5, by decide⟩ : Fin 222) := by decide
    have hbot : blockLabel j < (0 : Fin 41) := by
      rw [hflat] at hj
      change blockLabel j < (0 : Fin 41) at hj
      exact hj
    omega

#print axioms lowerRow
#print axioms supplementary_lowerRow
end
end AspisV8R19.R828SupplementarySourceLowerRows

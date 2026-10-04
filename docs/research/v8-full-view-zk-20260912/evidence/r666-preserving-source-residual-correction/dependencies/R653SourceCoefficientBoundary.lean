import AspisV8R19.R651ResidualKernelRepair
import Mathlib.Tactic
set_option autoImplicit false
namespace AspisV8R19.R653SourceCoefficientBoundary
open AspisR19 AspisV8R17 HighRepairInvariant BetaUniformCorrection
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

/-- Exact reversed-slot source kernel boundary, at arbitrary block count and
quarter scalar. No concrete recurrence or target compatibility is assumed. -/
theorem coefficient_boundary (n : Nat) (quarter : F)
    (q w : Fin n × Fin 4 → F) :
    coefficient (sourceKernel n 0 quarter) q w +
      coefficient (sourceKernel n 4 quarter) q w =
      quarter * (∑ d : Fin n, ∑ s : Fin 4, q (d,s) * w (d,s)) := by
  rw [FullCoefficientBoundary.coefficient_blocks, FullCoefficientBoundary.coefficient_blocks]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  simp [Fin.sum_univ_succ]
  ring

/-- Actual two-swap source weight contraction equals the low block dot.
The literal image tails are retained and vanish through flatten support. -/
theorem source_pairing_low (half a b c tau : F) (structured : Bool)
    (w : Fin 1024 → F) (q : Index 32 → F) :
    rangeDot 1024 (sourceQuotientWeights half
      (extendFin1024 (AspisV8R16.transportDual TwoSwapSourceTable.inactive 1023
        TwoSwapSourceTable.order w)) a b c tau structured) (NormalizedGCore.flatten q) =
      ∑ i : Index 32, q i * TwoSwapSourceWeights.blockWeight half a b c w i := by
  rw [FullResidualBoundary.flattened_pairing]
  apply Finset.sum_congr rfl
  intro i _
  rw [TwoSwapSourceWeights.quotient_entry half a b c tau structured w
    ⟨4*i.1.val+i.2.val,by omega⟩]
  rfl

/-- Zero source channel moment implies the exact coefficient-0/4 boundary,
without asserting that such a moment holds for an arbitrary source target. -/
theorem source_boundary_zero (half quarter a b c tau : F) (structured : Bool)
    (w : Fin 1024 → F) (q : Index 32 → F)
    (hm : rangeDot 1024 (sourceQuotientWeights half
      (extendFin1024 (AspisV8R16.transportDual TwoSwapSourceTable.inactive 1023
        TwoSwapSourceTable.order w)) a b c tau structured) (NormalizedGCore.flatten q) = 0) :
    coefficient (sourceKernel 32 0 quarter) q (TwoSwapSourceWeights.blockWeight half a b c w) +
      coefficient (sourceKernel 32 4 quarter) q (TwoSwapSourceWeights.blockWeight half a b c w) = 0 := by
  rw [source_pairing_low] at hm
  rw [coefficient_boundary]
  have hd : (∑ d : Fin 32, ∑ s : Fin 4,
      q (d,s) * TwoSwapSourceWeights.blockWeight half a b c w (d,s)) = 0 := by
    simpa only [Fintype.sum_prod_type] using hm
  rw [hd, mul_zero]

#print axioms coefficient_boundary
#print axioms source_pairing_low
#print axioms source_boundary_zero
end
end AspisV8R19.R653SourceCoefficientBoundary

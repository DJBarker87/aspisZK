import AspisV8R19.R660FullSourceResidualCorrection
import AspisV8R19.R574SparseGCorePolynomial
set_option autoImplicit false
namespace AspisV8R19.R661TwoSwapMaskAddition
open AspisR19 AspisV8R16 AspisV8R17 HighRepairInvariant
open R645TwoSwapHighDirections
open R649TwoSwapResidualRepair R650ResidualCombinationKernel
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

def fullMask (half a b c : F) (q : Nat → F) : Fin 1024 → F :=
  R562.inverseChordMessage half TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order q a b c

/-- Exact chord and balancing-permutation linearity for arbitrary full input,
using the selected two-swap routing. No source execution is asserted. -/
theorem full_mask_linear (half a b c u v : F) (q s : Nat → F) (r : Fin 1024) :
    fullMask half a b c (fun i => u*q i+v*s i) r =
      u*fullMask half a b c q r+v*fullMask half a b c s r := by
  unfold fullMask R562.inverseChordMessage inverseTransport
  simp only [R574SparseGCorePolynomial.sourceChord_linear]
  split_ifs
  · simp only [Finset.sum_add_distrib, Finset.mul_sum]
    ring
  · rfl

/-- Adding a flattened low correction to a full source quotient adds exactly
its existing actual mask, with no identification of two different permutations. -/
theorem full_mask_add_correction (half a b c : F) (q : Nat → F)
    (s : Index 32 → F) (r : Fin 1024) :
    fullMask half a b c (fun i => q i+NormalizedGCore.flatten s i) r =
      fullMask half a b c q r+actualMask half a b c s r := by
  have h := full_mask_linear half a b c (1:F) (1:F) q (NormalizedGCore.flatten s) r
  simpa only [one_mul] using h

/-- The complete 271 selected sparse mask coordinates of an arbitrary full
incoming G quotient are preserved by every exact residual combination. -/
theorem combined_sparse_coins_preserved (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (half alpha a b c : F)
    (x : Fin 13 → F) (q : Nat → F) (i : Fin 271) :
    actualCoin (fullMask half a b c
      (fun j => q j+NormalizedGCore.flatten (combination t ht noneOne alpha x) j)) i =
      actualCoin (fullMask half a b c q) i := by
  unfold actualCoin
  rw [full_mask_add_correction]
  have h := combination_sparse_coins_zero t ht noneOne half alpha a b c x i
  change actualMask half a b c (combination t ht noneOne alpha x)
    (TwoSwapSourceTable.order (TwoSwapSourceG.coinIndex i)) = 0 at h
  rw [h,add_zero]

/-- Every sparse terminal weighting is preserved, for arbitrary weights.
This is field-model correspondence, not publication or shared-oracle simulation. -/
theorem combined_sparse_pairing_preserved (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (half alpha a b c : F)
    (x : Fin 13 → F) (q : Nat → F) (weights : Fin 271 → F) :
    (∑ r : Fin 1024, TwoSwapSourceG.original weights r * fullMask half a b c
      (fun j => q j+NormalizedGCore.flatten (combination t ht noneOne alpha x) j) r) =
      ∑ r : Fin 1024, TwoSwapSourceG.original weights r * fullMask half a b c q r := by
  rw [R561.original_pairing, R561.original_pairing]
  apply Finset.sum_congr rfl
  intro i _
  change weights i * actualCoin (fullMask half a b c
    (fun j => q j+NormalizedGCore.flatten (combination t ht noneOne alpha x) j)) i =
      weights i * actualCoin (fullMask half a b c q) i
  rw [combined_sparse_coins_preserved]

/-- Inactive balance is preserved around any incoming full quotient. -/
theorem combined_balance_preserved (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (half alpha a b c : F)
    (x : Fin 13 → F) (q : Nat → F) :
    (∑ r ∈ TwoSwapSourceTable.inactive, fullMask half a b c
      (fun j => q j+NormalizedGCore.flatten (combination t ht noneOne alpha x) j) r) =
      ∑ r ∈ TwoSwapSourceTable.inactive, fullMask half a b c q r := by
  simp only [full_mask_add_correction, Finset.sum_add_distrib]
  rw [actual_mask_balanced,add_zero]

/-- A retained point whose correction is zero is preserved in the combined
source mask; the point-zero premise is supplied by R657/R660 when applicable. -/
theorem combined_point_preserved (half a b c : F) (q : Nat → F)
    (s : Index 32 → F) (point : Fin 10 → F)
    (hp : sourcePointFunctional point (actualMask half a b c s) = 0) :
    sourcePointFunctional point (fullMask half a b c (fun j => q j+NormalizedGCore.flatten s j)) =
      sourcePointFunctional point (fullMask half a b c q) := by
  simp only [sourcePointFunctional,full_mask_add_correction,mul_add,Finset.sum_add_distrib]
  change sourcePointFunctional point (fullMask half a b c q) +
    sourcePointFunctional point (actualMask half a b c s) = _
  rw [hp,add_zero]

#print axioms full_mask_linear
#print axioms full_mask_add_correction
#print axioms combined_sparse_coins_preserved
#print axioms combined_sparse_pairing_preserved
#print axioms combined_balance_preserved
#print axioms combined_point_preserved
end
end AspisV8R19.R661TwoSwapMaskAddition

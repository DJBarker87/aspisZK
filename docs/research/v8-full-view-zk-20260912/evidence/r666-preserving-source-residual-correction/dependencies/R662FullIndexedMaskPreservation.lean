import AspisV8R19.R661TwoSwapMaskAddition
set_option autoImplicit false
namespace AspisV8R19.R662FullIndexedMaskPreservation
open AspisR19 AspisV8R17 HighRepairInvariant
open R645TwoSwapHighDirections
open R649TwoSwapResidualRepair R650ResidualCombinationKernel
open R660FullSourceResidualCorrection R661TwoSwapMaskAddition
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

def flattenFull (q : Index 256 → F) (r : Nat) : F :=
  if h : r < 1024 then q (⟨r/4,by omega⟩,⟨r%4,Nat.mod_lt _ (by decide)⟩) else 0

def indexedMask (half a b c : F) (q : Index 256 → F) : Fin 1024 → F :=
  fullMask half a b c (flattenFull q)

/-- Exact connection between the 256-block full source correction and the
low flattening used by the selected residual mask theorem. -/
theorem flatten_full_add_correction (q : Index 256 → F) (s : Index 32 → F) (r : Nat) :
    flattenFull (fun i => q i+extendCorrection s i) r =
      flattenFull q r+NormalizedGCore.flatten s r := by
  by_cases hr : r < 1024
  · simp only [flattenFull,dif_pos hr,extendCorrection]
    rw [Nat.div_add_mod]
  · simp only [flattenFull,dif_neg hr,NormalizedGCore.flatten,dif_neg (by omega : ¬r<128),add_zero]

/-- The actual selected mask of the full indexed incoming G channel receives
exactly the low residual mask correction. No low support is assumed for G. -/
theorem indexed_mask_add_correction (half a b c : F) (q : Index 256 → F)
    (s : Index 32 → F) (r : Fin 1024) :
    indexedMask half a b c (fun i => q i+extendCorrection s i) r =
      indexedMask half a b c q r+actualMask half a b c s r := by
  unfold indexedMask
  have he : flattenFull (fun i => q i+extendCorrection s i) =
      fun j => flattenFull q j+NormalizedGCore.flatten s j := by
    funext j
    exact flatten_full_add_correction q s j
  rw [he,full_mask_add_correction]

/-- All sparse mask observations of the same full indexed G channel used by
R660 are preserved when the residual correction is added. -/
theorem indexed_sparse_coins_preserved (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (half alpha a b c : F)
    (x : Fin 13 → F) (q : Index 256 → F) (i : Fin 271) :
    actualCoin (indexedMask half a b c
      (fun j => q j+extendCorrection (combination t ht noneOne alpha x) j)) i =
      actualCoin (indexedMask half a b c q) i := by
  unfold actualCoin
  rw [indexed_mask_add_correction]
  have h := combination_sparse_coins_zero t ht noneOne half alpha a b c x i
  change actualMask half a b c (combination t ht noneOne alpha x)
    (TwoSwapSourceTable.order (TwoSwapSourceG.coinIndex i)) = 0 at h
  rw [h,add_zero]

theorem indexed_balance_preserved (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (half alpha a b c : F)
    (x : Fin 13 → F) (q : Index 256 → F) :
    (∑ r ∈ TwoSwapSourceTable.inactive, indexedMask half a b c
      (fun j => q j+extendCorrection (combination t ht noneOne alpha x) j) r) =
      ∑ r ∈ TwoSwapSourceTable.inactive, indexedMask half a b c q r := by
  simp only [indexed_mask_add_correction,Finset.sum_add_distrib]
  rw [actual_mask_balanced,add_zero]

theorem indexed_point_preserved (half a b c : F) (q : Index 256 → F)
    (s : Index 32 → F) (point : Fin 10 → F)
    (hp : sourcePointFunctional point (actualMask half a b c s) = 0) :
    sourcePointFunctional point (indexedMask half a b c (fun j => q j+extendCorrection s j)) =
      sourcePointFunctional point (indexedMask half a b c q) := by
  simp only [sourcePointFunctional,indexed_mask_add_correction,mul_add,Finset.sum_add_distrib]
  change sourcePointFunctional point (indexedMask half a b c q) +
    sourcePointFunctional point (actualMask half a b c s) = _
  rw [hp,add_zero]
  rfl

#print axioms flatten_full_add_correction
#print axioms indexed_mask_add_correction
#print axioms indexed_sparse_coins_preserved
#print axioms indexed_balance_preserved
#print axioms indexed_point_preserved
end
end AspisV8R19.R662FullIndexedMaskPreservation

import AspisV8R19.R830JointCombinationTail
import AspisV8R19.R727TopBalance
import AspisV8R19.R738JointObservationModel

set_option autoImplicit false
namespace AspisV8R19.R831JointCombinationBalance
open AspisV8R19.R826JointCombinationObservation
open AspisV8R19.R830JointCombinationTail
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R662FullIndexedMaskPreservation
open AspisV8R19.R727TopBalance
open AspisV8R17
open AspisR19
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]
abbrev ObservationRow := R738JointObservationModel.ObservationRow

theorem flatten_combination_top (alpha : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (x : ObservationRow → F) (r : Nat) (hr : 1020 ≤ r) :
    flattenFull (combination alpha t ht noneOne x) r = 0 := by
  by_cases htop : r < 1024
  · rw [flattenFull, dif_pos htop]
    have hd : r / 4 = 255 := by omega
    have hi : (⟨r / 4, by omega⟩ : Fin 256) = (255 : Fin 256) := Fin.ext hd
    rw [hi]
    simpa using combination_degree255 alpha t ht noneOne x
      ⟨r % 4, Nat.mod_lt _ (by decide)⟩
  · rw [flattenFull, dif_neg htop]

theorem rawMask_combination_balanced (half a b c alpha : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (x : ObservationRow → F) :
    (∑ r ∈ TwoSwapSourceTable.inactive,
      rawMask half a b c (combination alpha t ht noneOne x) r) = 0 := by
  rw [rawMask_eq_indexedMask]
  exact indexed_balance_from_top half a b c (combination alpha t ht noneOne x)
    (flatten_combination_top alpha t ht noneOne x 1021 (by omega))
    (flatten_combination_top alpha t ht noneOne x 1022 (by omega))
    (flatten_combination_top alpha t ht noneOne x 1023 (by omega))

#print axioms flatten_combination_top
#print axioms rawMask_combination_balanced
end
end AspisV8R19.R831JointCombinationBalance

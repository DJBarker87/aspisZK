import AspisV8R19.R727TopBalance

set_option autoImplicit false
namespace AspisV8R19.R728BalancedImageTails
open AspisV8R17 AspisV8R16 AspisR19
open HighRepairInvariant R662FullIndexedMaskPreservation R727TopBalance
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2:F)]

theorem indexed_balance_eq (half a b c : F) (q : Index 256 → F) :
    (∑ r ∈ TwoSwapSourceTable.inactive, indexedMask half a b c q r)=
      c*flattenFull q 1022+a*flattenFull q 1023+b*flattenFull q 1021 := by
  have ht := congrFun (transport_inverse TwoSwapSourceTable.inactive 1023
    TwoSwapSourceTable.pivot_inactive TwoSwapSourceTable.order
    (fun j : Fin 1024 => sourceChord half (flattenFull q) a b c j.val)) (1023:Fin 1024)
  change transport TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order
    (indexedMask half a b c q) 1023 = sourceChord half (flattenFull q) a b c 1023 at ht
  rw [transport, TwoSwapSourceTable.pivot_fixed, if_pos rfl] at ht
  exact ht.trans (sourceChord_last half a b c (flattenFull q))

theorem balanced_image_tails (half a b c alpha : F) (q : Index 256 → F)
    (h23 : flattenFull q 1023=0)
    (himage : b*flattenFull q 1022-c*flattenFull q 1021=0)
    (hbalance : (∑ r ∈ TwoSwapSourceTable.inactive, indexedMask half a b c q r)=0)
    (hnorm : b^2+c^2≠0)
    (hfold : R370KernelEvaluation.firstFold 256 alpha q 255=0) :
    flattenFull q 1020=0 ∧ flattenFull q 1021=0 ∧
      flattenFull q 1022=0 ∧ flattenFull q 1023=0 := by
  rw [indexed_balance_eq, h23, mul_zero, add_zero] at hbalance
  have h21mul : flattenFull q 1021*(b^2+c^2)=0 := by
    linear_combination b*hbalance-c*himage
  have h22mul : flattenFull q 1022*(b^2+c^2)=0 := by
    linear_combination c*hbalance+b*himage
  have h21 := (mul_eq_zero.mp h21mul).resolve_right hnorm
  have h22 := (mul_eq_zero.mp h22mul).resolve_right hnorm
  have h20 : flattenFull q 1020=0 := by
    simp only [flattenFull, dif_pos (by decide : 1021<1024)] at h21
    simp only [flattenFull, dif_pos (by decide : 1022<1024)] at h22
    simp only [flattenFull, dif_pos (by decide : 1023<1024)] at h23
    simpa [flattenFull, R370KernelEvaluation.firstFold, Fin.sum_univ_succ,
      h21, h22, h23] using hfold
  exact ⟨h20,h21,h22,h23⟩

theorem circle_norm_factor (u v : F) :
    (u*v-1)^2+(-(u+v))^2=(1+u^2)*(1+v^2) := by ring

theorem circle_norm_ne_zero (u v : F) (hu : 1+u^2≠0) (hv : 1+v^2≠0) :
    (u*v-1)^2+(-(u+v))^2≠0 := by
  rw [circle_norm_factor]
  exact mul_ne_zero hu hv

#print axioms indexed_balance_eq
#print axioms balanced_image_tails
#print axioms circle_norm_factor
#print axioms circle_norm_ne_zero
end
end AspisV8R19.R728BalancedImageTails

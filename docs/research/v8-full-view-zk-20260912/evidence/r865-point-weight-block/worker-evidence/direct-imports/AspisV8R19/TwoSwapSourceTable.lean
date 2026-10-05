import AspisV8R19.T163SourceTable
import AspisV8R19.TwoSwapWitnessData

/-! New permutation, unchanged source inventory. The large T163 ordering
is not reused. Inverses are proved from digit arithmetic, not enumeration of
field terms. Literal source/table agreement is audited separately. -/
set_option autoImplicit false
namespace AspisR19.TwoSwapSourceTable

def baseNat (j : Nat) : Nat := j%2+16*((j/2)%64)+2*(7-j/128)
def backNat (r : Nat) : Nat := r%2+2*(r/16)+128*(7-(r/2)%8)

theorem base_bound (j : Fin 1024) : baseNat j.val<1024 := by
  have := j.isLt
  dsimp [baseNat]
  omega
theorem back_bound (j : Fin 1024) : backNat j.val<1024 := by
  have := j.isLt
  dsimp [backNat]
  omega
theorem back_base (j : Fin 1024) : backNat (baseNat j.val)=j.val := by
  have := j.isLt
  have hd := Nat.div_div_eq_div_mul j.val 2 64
  have he := Nat.div_div_eq_div_mul (baseNat j.val) 2 8
  dsimp [baseNat,backNat] at *
  omega
theorem base_back (j : Fin 1024) : baseNat (backNat j.val)=j.val := by
  have := j.isLt
  have hd := Nat.div_div_eq_div_mul j.val 2 8
  have he := Nat.div_div_eq_div_mul (backNat j.val) 2 64
  dsimp [baseNat,backNat] at *
  omega

def base : Equiv.Perm (Fin 1024) where
  toFun j := ⟨baseNat j.val,base_bound j⟩
  invFun j := ⟨backNat j.val,back_bound j⟩
  left_inv j := Fin.ext (back_base j)
  right_inv j := Fin.ext (base_back j)

def order : Equiv.Perm (Fin 1024) :=
  (Equiv.swap 127 1023).trans ((Equiv.swap 126 1021).trans base)

abbrev isInactive := T163SourceTable.isInactive
abbrev inactive := T163SourceTable.inactive

theorem pivot_fixed : order (1023:Fin 1024)=1023 := by decide
theorem pivot_inactive : (1023:Fin 1024)∈inactive := T163SourceTable.pivot_inactive

def lowIndex (j : Fin 131) : Fin 1024 := ⟨j.val,by omega⟩
theorem low_not_pivot (j : Fin 131) : order (lowIndex j)≠1023 := by
  intro h
  have he := congrArg Fin.val (order.injective (h.trans pivot_fixed.symm))
  have hj:=j.isLt
  simp only [lowIndex] at he
  omega

theorem residual_order (j : Fin 131) :
    (order (lowIndex j)).val=TwoSwapWitness.orderValue j.val := by
  revert j; decide
theorem residual_inactive (j : Fin 131) :
    isInactive (order (lowIndex j))=TwoSwapWitness.inactiveValue j.val := by
  revert j; decide
theorem first_pad_images (j : Fin 89) :
    (order ⟨j.val,by omega⟩).val=16*(j.val/2)+14+j.val%2 := by
  revert j; decide

#print axioms base_bound
#print axioms back_bound
#print axioms back_base
#print axioms base_back
#print axioms pivot_fixed
#print axioms pivot_inactive
#print axioms low_not_pivot
#print axioms residual_order
#print axioms residual_inactive
#print axioms first_pad_images
end AspisR19.TwoSwapSourceTable

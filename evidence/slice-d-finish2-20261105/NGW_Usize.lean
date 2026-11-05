import NGM_ScalarCanon
set_option autoImplicit false
namespace NGW_Usize
open Aeneas Aeneas.Std Result

theorem sub_value (x y : Usize) (h : y.val≤x.val) :
 (Usize.wrapping_sub x y).val=x.val-y.val := by
 rw [Usize.wrapping_sub_val_eq]
 have hx := x.hSize
 have hy := y.hSize
 have rearrange : x.val+(UScalar.size .Usize-y.val)=(x.val-y.val)+UScalar.size .Usize := by omega
 rw [rearrange,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod,Nat.mod_eq_of_lt (by omega)]

#print axioms sub_value
end NGW_Usize

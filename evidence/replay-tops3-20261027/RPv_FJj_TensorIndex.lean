import RPv_FJj_TensorCell
set_option autoImplicit false
namespace AspisR1.FJj_TensorIndex
open Aeneas Aeneas.Std

theorem value (j n s : Usize) (hn : n.val≤16) (hj : j.val < n.val) (hs : s.val<4) :
    (FJj_TensorCell.index j n s).val=j.val+s.val*n.val := by
  have size : 4096≤UScalar.size .Usize := by
    rw [UScalar.size_def,UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with h|h <;> simp [h]
  have prod : s.val*n.val≤3*16 := Nat.mul_le_mul (by omega) hn
  have hp : s.val*n.val<UScalar.size .Usize := by omega
  have ht : j.val+s.val*n.val<UScalar.size .Usize := by omega
  rw [FJj_TensorCell.index,Usize.wrapping_add_val_eq,Usize.wrapping_mul_val_eq,
    Nat.mod_eq_of_lt hp,Nat.mod_eq_of_lt ht]
#print axioms value
end AspisR1.FJj_TensorIndex

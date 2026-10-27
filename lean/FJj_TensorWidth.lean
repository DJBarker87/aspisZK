import FJj_TensorIndex
set_option autoImplicit false
namespace AspisR1.FJj_TensorWidth
open Aeneas Aeneas.Std

theorem value (n : Usize) (hn : n.val≤16) :
    (Usize.wrapping_mul n 4#usize).val=4*n.val := by
  have size : 4096≤UScalar.size .Usize := by
    rw [UScalar.size_def,UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with h|h <;> simp [h]
  rw [Usize.wrapping_mul_val_eq,show (4#usize).val=4 from by decide,
    Nat.mod_eq_of_lt (show n.val*4<UScalar.size .Usize by omega)]
  omega
#print axioms value
end AspisR1.FJj_TensorWidth

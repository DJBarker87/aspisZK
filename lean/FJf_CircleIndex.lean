import FJf_Coordinates
set_option autoImplicit false
namespace AspisR1.FJf_CircleIndex
open Aeneas Aeneas.Std

theorem value (k : Usize) (hk : k.val < 2) :
    (Usize.wrapping_add 3#usize k).val=3+k.val := by
  have size : 16≤UScalar.size .Usize := by
    rw [UScalar.size_def,UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with h|h <;> simp [h]
  rw [Usize.wrapping_add_val_eq,show (3#usize).val=3 from by scalar_tac,
    Nat.mod_eq_of_lt (by omega)]
#print axioms value
end AspisR1.FJf_CircleIndex

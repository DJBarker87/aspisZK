import FJc_ByteCarrier
set_option autoImplicit false
namespace AspisR1.FJc_FieldOffsets
open Aeneas Aeneas.Std
/-- Deployed Pair reads fewer than 64 fields, so both native wrapping offsets
are exactly the intended mathematical offsets. -/
theorem value (i : Usize) (hi : i.val<64) :
    (Usize.wrapping_mul i 32#usize).val=32*i.val ∧
    (Usize.wrapping_mul (Usize.wrapping_add i 1#usize) 32#usize).val=32*(i.val+1) := by
  have h1 : i.val+1<UScalar.size .Usize := by scalar_tac
  have h2 : i.val*32<UScalar.size .Usize := by scalar_tac
  have h3 : (i.val+1)*32<UScalar.size .Usize := by scalar_tac
  constructor
  · rw [UScalar.wrapping_mul_val_eq,Nat.mod_eq_of_lt h2];omega
  · rw [UScalar.wrapping_mul_val_eq,UScalar.wrapping_add_val_eq,
      Nat.mod_eq_of_lt h1,Nat.mod_eq_of_lt h3];omega
#print axioms value
end AspisR1.FJc_FieldOffsets

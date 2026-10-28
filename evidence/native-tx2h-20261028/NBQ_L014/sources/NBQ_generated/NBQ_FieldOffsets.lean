import FIo_NativeFuns
set_option autoImplicit false
namespace NBQ_FieldOffsets
open Aeneas Aeneas.Std
/-- Every valid selected range, with no arbitrary64-row restriction. -/
theorem value (i : Usize) (fits : 32*(i.val+1)<UScalar.size .Usize) :
    (Usize.wrapping_mul i 32#usize).val=32*i.val ∧
    (Usize.wrapping_mul (Usize.wrapping_add i 1#usize) 32#usize).val=32*(i.val+1) := by
  have h1 : i.val+1<UScalar.size .Usize := by omega
  have h2 : i.val*32<UScalar.size .Usize := by omega
  have h3 : (i.val+1)*32<UScalar.size .Usize := by omega
  have v32 : (32#usize).val=32 := by scalar_tac
  have v1 : (1#usize).val=1 := by scalar_tac
  constructor
  · rw [Usize.wrapping_mul_val_eq,v32,Nat.mod_eq_of_lt h2];omega
  · rw [Usize.wrapping_mul_val_eq,Usize.wrapping_add_val_eq,v1,v32,
      Nat.mod_eq_of_lt h1,Nat.mod_eq_of_lt h3];omega
#print axioms value
end NBQ_FieldOffsets

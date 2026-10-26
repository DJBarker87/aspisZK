import PoolW_ZeroStep
set_option autoImplicit false
namespace AspisR1.PoolW_ZeroArithmetic
open Aeneas Aeneas.Std Result ControlFlow

theorem increment (bytes : Slice U8) (i : Usize)
    (within : i < Slice.len bytes) :
    (Usize.wrapping_add i 1#usize).val = i.val + 1 := by
  have size := bytes.property
  have range : i.val + 1 ≤ Usize.max := by scalar_tac
  rw [Usize.wrapping_add_val_eq]
  have strict : i.val + (1#usize).val < UScalar.size .Usize := by scalar_tac
  rw [Nat.mod_eq_of_lt strict]
  rfl

#print axioms increment
end AspisR1.PoolW_ZeroArithmetic

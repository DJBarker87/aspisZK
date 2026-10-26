import PoolW_ZeroStep
set_option autoImplicit false
namespace AspisR1.PoolW_ZeroArithmetic
open Aeneas Aeneas.Std Result ControlFlow

theorem increment (bytes : Slice U8) (i : Usize)
    (within : i < Slice.len bytes) :
    (Usize.wrapping_add i 1#usize).val = i.val + 1 := by
  have size := bytes.property
  have range : i.val + 1 ≤ Usize.max := by scalar_tac
  simp [Usize.wrapping_add, UScalar.wrapping_add, UScalar.ofNat, Nat.mod_eq_of_lt] <;> scalar_tac

#print axioms increment
end AspisR1.PoolW_ZeroArithmetic

import R1Z.ProverRwP7CurrentFieldSource
set_option autoImplicit false
namespace R1Z.ProverRwP7CurrentCtApi
open Aeneas Aeneas.Std

theorem add (a b : U32) : core.num.U32.wrapping_add a b = U32.wrapping_add a b := by
  apply UScalar.eq_of_val_eq
  rw [core.num.U32.wrapping_add_val_eq,U32.wrapping_add_val_eq]

theorem sub (a b : U32) : core.num.U32.wrapping_sub a b = U32.wrapping_sub a b := by
  apply UScalar.eq_of_val_eq
  rw [core.num.U32.wrapping_sub_val_eq,U32.wrapping_sub_val_eq]
#print axioms add
#print axioms sub
end R1Z.ProverRwP7CurrentCtApi

import R1Z.PV_RunJoin_WeightCarrier46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightWrapping46
open Aeneas Aeneas.Std

theorem add (a b : U32) : core.num.U32.wrapping_add a b=U32.wrapping_add a b := by
  apply UScalar.eq_of_val_eq
  rw [core.num.U32.wrapping_add_val_eq,U32.wrapping_add_val_eq]

theorem sub (a b : U32) : core.num.U32.wrapping_sub a b=U32.wrapping_sub a b := by
  apply UScalar.eq_of_val_eq
  rw [core.num.U32.wrapping_sub_val_eq,U32.wrapping_sub_val_eq]
#print axioms add
#print axioms sub
#print core.num.U32.wrapping_add
#print core.num.U32.wrapping_sub
end R1Z.PV_RunJoin_WeightWrapping46

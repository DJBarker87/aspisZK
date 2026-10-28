import PV_B3P_E227_01
namespace PV_B3P_FieldBase227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

def subtract (x : U32) : U32 :=
  let bit := UScalar.cast_fromBool .U32 (x >= aspis_core.field.P)
  let mask := core.num.U32.wrapping_sub 0#u32 bit
  core.num.U32.wrapping_sub x (aspis_core.field.P &&& mask)

def reduce (x : U64) : U32 :=
  let p := UScalar.cast .U64 aspis_core.field.P
  let y := U64.wrapping_add (x &&& p) (U64.wrapping_shr x 31#u32)
  let z := U64.wrapping_add (y &&& p) (U64.wrapping_shr y 31#u32)
  subtract (UScalar.cast .U32 z)

def add (x y : U32) : U32 := subtract (core.num.U32.wrapping_add x y)
def sub (x y : U32) : U32 :=
  subtract (core.num.U32.wrapping_sub (core.num.U32.wrapping_add x aspis_core.field.P) y)
def mul (x y : U32) : U32 :=
  reduce (U64.wrapping_mul (UScalar.cast .U64 x) (UScalar.cast .U64 y))

theorem subtract_result (x : U32) : aspis_core.field.ct.subtract_p x = .ok (subtract x) := rfl
theorem reduce_result (x : U64) : aspis_core.field.ct.reduce64 x = .ok (reduce x) := rfl
theorem ct_add_result (x y : U32) : aspis_core.field.ct.add x y = .ok (add x y) := rfl
theorem ct_sub_result (x y : U32) : aspis_core.field.ct.sub x y = .ok (sub x y) := rfl

theorem add_result (x y : U32) : aspis_core.field.M31.add x y = .ok (add x y) := rfl
theorem mul_result (x y : U32) : aspis_core.field.M31.mul x y = .ok (mul x y) := rfl
theorem reduce64_result (x : U64) : aspis_core.field.M31.reduce_u64 x = .ok (reduce x) := rfl
theorem reduce62_result (x : U64) : aspis_core.field.M31.reduce_u62 x = .ok (reduce x) := rfl
theorem double_result (x : U32) : aspis_core.field.M31.double x = .ok (add x x) := rfl

#print axioms subtract_result
#print axioms reduce_result
#print axioms ct_add_result
#print axioms ct_sub_result
#print axioms add_result
#print axioms mul_result
#print axioms reduce64_result
#print axioms reduce62_result
#print axioms double_result
end PV_B3P_FieldBase227

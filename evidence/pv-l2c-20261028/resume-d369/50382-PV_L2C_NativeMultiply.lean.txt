import PV_L2C_NativeReduce
set_option autoImplicit false
namespace PV_L2C_NativeMultiply
open PV_L2C_M31

def wide (x : word) : BitVec 64 := x.setWidth 64

theorem widened (x : word) : (wide x).toNat = x.toNat := by
  rw [wide,BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have hx := x.isLt;omega)
#print axioms widened

theorem product_bound (x y : word) : x.toNat*y.toNat < 2^64 := by
  have hx := x.isLt
  have hy := y.isLt
  calc
    x.toNat*y.toNat ≤ (2^32-1)*(2^32-1) := Nat.mul_le_mul (by omega) (by omega)
    _ < 2^64 := by norm_num
#print axioms product_bound

def mul (x y : word) : word := PV_L2C_NativeReduce.run (wide x*wide y)

theorem canonical_result (x y : word) : canonical (mul x y) :=
  PV_L2C_NativeReduce.canonical_result _
#print axioms canonical_result

theorem decoded (x y : word) : decode (mul x y) = decode x*decode y := by
  rw [mul,PV_L2C_NativeReduce.field_result,BitVec.toNat_mul,widened,widened,
    Nat.mod_eq_of_lt (product_bound x y),Nat.cast_mul]
  rfl
#print axioms decoded
end PV_L2C_NativeMultiply

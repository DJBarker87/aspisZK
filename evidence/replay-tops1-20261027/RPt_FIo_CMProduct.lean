import RPt_FIo_CMValues
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.FIo_CMProduct
open FIo_FieldBridge (NC)

def sum (x : NC) : U64 := U64.wrapping_add
  (core.convert.num.FromU64U32.from x.a) (core.convert.num.FromU64U32.from x.b)

def cross (x y : NC) : U64 := U64.wrapping_mul (sum x) (sum y)

theorem sum_value (x : NC) : (sum x).val=x.a.val+x.b.val := by
  unfold sum
  rw [U64.wrapping_add_val_eq,Nat.mod_eq_of_lt (by scalar_tac)]
  rfl

theorem sum_bound (x : NC) (hx : FIo_CMValues.Canon x) : (sum x).val≤4294967292 := by
  rw [sum_value]
  obtain ⟨a,b⟩ := hx
  omega

theorem cross_value (x y : NC) (hx : FIo_CMValues.Canon x) (hy : FIo_CMValues.Canon y) :
    (cross x y).val=(x.a.val+x.b.val)*(y.a.val+y.b.val) := by
  have bound := Nat.mul_le_mul (sum_bound x hx) (sum_bound y hy)
  unfold cross
  rw [U64.wrapping_mul_val_eq,Nat.mod_eq_of_lt (by scalar_tac),sum_value,sum_value]

#print axioms sum_value
#print axioms sum_bound
#print axioms cross_value
end AspisR1.FIo_CMProduct

import AspisV8R19.R250PrivateBaseExecution

/-! Canonical private complex norm execution, preserving its unreduced
wide sum before reduction. No private product, coefficients or inverse. -/
set_option autoImplicit false
namespace AspisV8R19.R253PrivateComplexNorm
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase (M31Exact CM31Exact P)
open AspisR249R110Raw.circle_norm.joined_inverse.line_norm.r110_norm (C)
open R250PrivateBaseExecution (encodeC)
open R163ComplexExecution (wide wide_value)
open ComplexBaseExecution (encodeBase)
noncomputable section

theorem square_bound (x : M31Exact) : x.val*x.val < P*P :=
  CanonicalProduct.product_lt _ _ (ZMod.val_lt x) (ZMod.val_lt x)

theorem wide_square (x : M31Exact) :
    (U64.wrapping_mul (wide x) (wide x)).val = x.val*x.val := by
  have hx := square_bound x
  have hb : (wide x).val*(wide x).val < 2^64 := by
    simp only [wide_value]
    unfold P at hx
    omega
  rw [R161WrappedMulExecution.mul64_val _ _ hb,wide_value]

theorem square_sum_bound (x y : M31Exact) :
    x.val*x.val+y.val*y.val < 2^64 := by
  have hx := square_bound x
  have hy := square_bound y
  unfold P at hx hy
  omega

theorem c_norm (z : CM31Exact) :
    C.norm (encodeC z) = .ok (encodeBase (NormInverse.complexNorm z)) := by
  let a := U64.wrapping_mul (wide z.re) (wide z.re)
  let b := U64.wrapping_mul (wide z.im) (wide z.im)
  have ha : a.val=z.re.val*z.re.val := wide_square z.re
  have hb : b.val=z.im.val*z.im.val := wide_square z.im
  have hab : a.val+b.val<2^64 := by
    rw [ha,hb]; exact square_sum_bound z.re z.im
  have hs : (U64.wrapping_add a b).val=
      z.re.val*z.re.val+z.im.val*z.im.val := by
    rw [R159WideBaseExecution.add64_val _ _ hab,ha,hb]
  simp only [C.norm,encodeC,lift,bind_tc_ok,R250PrivateBaseExecution.reduce_encoded]
  change (Result.ok (encodeBase ((U64.wrapping_add a b).val : M31Exact)) : Result U32) = _
  simp only [hs,Nat.cast_add,Nat.cast_mul,ZMod.natCast_zmod_val]
  rfl

#print axioms square_bound
#print axioms wide_square
#print axioms square_sum_bound
#print axioms c_norm
end
end AspisV8R19.R253PrivateComplexNorm

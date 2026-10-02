import AspisV8R19.R253PrivateComplexNorm

/-! Private source complex multiplication: bounded unreduced wide terms,
including the checked PP constant, before the actual reduction. -/
set_option autoImplicit false
namespace AspisV8R19.R258PrivateProduct
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase (M31Exact CM31Exact P)
open AspisR249R110Raw.circle_norm.joined_inverse.line_norm.r110_norm (B C P110)
open R250PrivateBaseExecution (encodeC)
open ComplexBaseExecution (encodeBase)
open R163ComplexExecution (wide wide_value)
noncomputable section

theorem product_bound (x y : M31Exact) : x.val*y.val < P*P :=
  CanonicalProduct.product_lt _ _ (ZMod.val_lt x) (ZMod.val_lt y)

theorem wide_product (x y : M31Exact) :
    (U64.wrapping_mul (wide x) (wide y)).val = x.val*y.val := by
  have hp := product_bound x y
  have hb : (wide x).val*(wide y).val < 2^64 := by
    simp only [wide_value]
    unfold P at hp
    omega
  rw [R161WrappedMulExecution.mul64_val _ _ hb]
  simp only [wide_value]

abbrev pw : U64 := core.convert.num.FromU64U32.from P110
abbrev ppw : U64 := U64.wrapping_mul pw pw

theorem pw_val : pw.val = P := by
  rw [core.convert.num.FromU64U32.from_val_eq,R250PrivateBaseExecution.p110_val]

theorem ppw_val : ppw.val = P*P := by
  unfold ppw
  rw [R161WrappedMulExecution.mul64_val, pw_val]
  rw [pw_val]
  unfold P
  omega

theorem pp_ok : C.mul.PP = .ok ppw := by
  have hb : pw.val*pw.val<2^64 := by rw [pw_val]; unfold P; omega
  obtain ⟨v,hv,hvv⟩ := InverseRuntimeMul.mul_success pw pw hb
  have he : v=ppw := by
    apply UScalar.eq_of_val_eq
    rw [hvv,pw_val,ppw_val]
  simp only [C.mul.PP,lift,bind_tc_ok]
  change (pw*pw : Result U64) = Result.ok ppw
  exact hv.trans (congrArg Result.ok he)

theorem real_wide (a b c d : M31Exact) :
    (U64.wrapping_sub
      (U64.wrapping_add (U64.wrapping_mul (wide a) (wide c)) ppw)
      (U64.wrapping_mul (wide b) (wide d))).val =
        a.val*c.val+P*P-b.val*d.val := by
  have hac := product_bound a c
  have hbd := product_bound b d
  have hsum : (U64.wrapping_mul (wide a) (wide c)).val+ppw.val<2^64 := by
    rw [wide_product,ppw_val]; unfold P at hac ⊢; omega
  have hs := R159WideBaseExecution.add64_val _ _ hsum
  have hge : (U64.wrapping_mul (wide b) (wide d)).val ≤
      (U64.wrapping_add (U64.wrapping_mul (wide a) (wide c)) ppw).val := by
    rw [hs,wide_product,wide_product,ppw_val]; omega
  rw [R159WideBaseExecution.sub64_val _ _ hge,hs,wide_product,wide_product,ppw_val]

theorem imag_wide (a b c d : M31Exact) :
    (U64.wrapping_add (U64.wrapping_mul (wide a) (wide d))
      (U64.wrapping_mul (wide b) (wide c))).val =
        a.val*d.val+b.val*c.val := by
  have had := product_bound a d
  have hbc := product_bound b c
  have hs : (U64.wrapping_mul (wide a) (wide d)).val+
      (U64.wrapping_mul (wide b) (wide c)).val<2^64 := by
    rw [wide_product,wide_product]; unfold P at had hbc; omega
  rw [R159WideBaseExecution.add64_val _ _ hs,wide_product,wide_product]

theorem c_mul (z w : CM31Exact) :
    C.mul (encodeC z) (encodeC w) = .ok (encodeC (z*w)) := by
  have hbd := product_bound z.im w.im
  have hge : z.im.val*w.im.val ≤ z.re.val*w.re.val+P*P := by omega
  have hp : (P : M31Exact)=0 := by simp [P,M31Exact]
  have hre : (((U64.wrapping_sub
      (U64.wrapping_add (U64.wrapping_mul (wide z.re) (wide w.re)) ppw)
      (U64.wrapping_mul (wide z.im) (wide w.im))).val : Nat) : M31Exact) =
      z.re*w.re-z.im*w.im := by
    rw [real_wide,Nat.cast_sub hge,Nat.cast_add,Nat.cast_mul,Nat.cast_mul,Nat.cast_mul]
    simp only [ZMod.natCast_zmod_val,hp,mul_zero,add_zero]
  have him : (((U64.wrapping_add
      (U64.wrapping_mul (wide z.re) (wide w.im))
      (U64.wrapping_mul (wide z.im) (wide w.re))).val : Nat) : M31Exact) =
      z.re*w.im+z.im*w.re := by
    rw [imag_wide,Nat.cast_add,Nat.cast_mul,Nat.cast_mul]
    simp only [ZMod.natCast_zmod_val]
  simp only [C.mul,encodeC,lift,bind_tc_ok,pp_ok,
    R250PrivateBaseExecution.reduce_encoded]
  change (Result.ok (encodeBase _,encodeBase _) : Result C) = _
  rw [hre,him]
  congr 1
  apply Prod.ext <;> congr 1 <;>
    simp [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul] <;> ring

#print axioms product_bound
#print axioms wide_product
#print axioms pw_val
#print axioms ppw_val
#print axioms pp_ok
#print axioms real_wide
#print axioms imag_wide
#print axioms c_mul
end
end AspisV8R19.R258PrivateProduct

import AspisV8R19.R251PrivateAddSub
import AspisV8R19.R163ComplexExecution

/-! Exact selected execution of the private R110 complex square leaf. -/
set_option autoImplicit false
namespace AspisV8R19.R257PrivateSquare
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase (CM31Exact M31Exact P)
open AspisR249R110Raw.circle_norm.joined_inverse.line_norm.r110_norm (B C P110)
open ComplexBaseExecution (encodeBase)
noncomputable section

theorem c_square (z : CM31Exact) :
    C.square (AspisV8R19.R250PrivateBaseExecution.encodeC z) =
      .ok (AspisV8R19.R250PrivateBaseExecution.encodeC (z*z)) := by
  obtain ⟨s, hs, hsv, hsb⟩ := AspisV8R19.R163ComplexExecution.raw_sum z.re z.im
  obtain ⟨a, t, ha, ht, htv, htb⟩ :=
    AspisV8R19.R163ComplexExecution.raw_difference z.re z.im
  have hp110 : P110 = AspisR156FullFreeze.aspis_core.field.P := by
    apply UScalar.eq_of_val_eq
    simp [AspisV8R19.R250PrivateBaseExecution.p110_val,
      AspisV8R19.R159WideBaseExecution.p_val,
      AspisR156FullFreeze.aspis_core.field.P, P]
  have hprod : s.val * t.val < 2^64 := by
    have hst : s.val * t.val < (2^32) * (2^32) :=
      Nat.mul_lt_mul_of_lt_of_lt hsb htb
    calc
      s.val * t.val < (2^32) * (2^32) := hst
      _ ≤ 2^64 := by norm_num
  have hm := AspisV8R19.R161WrappedMulExecution.mul64_val s t hprod
  have him_lt : z.im.val < P := ZMod.val_lt z.im
  have hle : z.im.val ≤ z.re.val + P := by omega
  have hcast : (t.val : M31Exact) = z.re - z.im := by
    rw [htv, Nat.cast_sub hle, Nat.cast_add,
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    simp [P, M31Exact]
  have hfirst : B.reduce (U64.wrapping_mul s t) =
      .ok (encodeBase ((z.re + z.im) * (z.re - z.im))) := by
    rw [AspisV8R19.R250PrivateBaseExecution.reduce_encoded, hm]
    congr 1
    rw [Nat.cast_mul, hsv, Nat.cast_add,
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, hcast]
  have hcomplex :
      (⟨(z.re + z.im) * (z.re - z.im), z.re * z.im + z.re * z.im⟩ : CM31Exact) = z*z := by
    apply QuadraticAlgebra.ext <;>
      simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;> ring
  calc
    C.square (AspisV8R19.R250PrivateBaseExecution.encodeC z) =
        .ok (AspisV8R19.R250PrivateBaseExecution.encodeC
          ⟨(z.re + z.im) * (z.re - z.im), z.re * z.im + z.re * z.im⟩) := by
      simp [C.square, AspisV8R19.R250PrivateBaseExecution.encodeC,
        lift, bind_tc_ok, hs, hp110, ha, ht, hfirst,
        AspisV8R19.R250PrivateBaseExecution.mul_encoded,
        AspisV8R19.R251PrivateAddSub.b_add_encode]
    _ = .ok (AspisV8R19.R250PrivateBaseExecution.encodeC (z*z)) := by
      rw [hcomplex]

#print axioms c_square
end
end AspisV8R19.R257PrivateSquare

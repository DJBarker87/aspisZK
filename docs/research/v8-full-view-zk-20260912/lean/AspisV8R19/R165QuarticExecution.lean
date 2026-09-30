import AspisV8R19.R164ProductExecution

/-! Selected QM31 field operations and exact canonical representation.
The selected square uses its proved canonical product path; no old square
implementation or runtime success is assumed. -/
set_option autoImplicit false
namespace AspisV8R19.R165QuarticExecution
open Aeneas Aeneas.Std Result
open AspisR156FullFreeze.aspis_core
open AspisV8R15.ExactTowerBase
open R164ProductExecution (encode public_product)
open R163ComplexExecution (cm_add cm_sub cm_neg cm_mul cm_square cm_mul_r cm_inv cm_zero_test)
noncomputable section

theorem zero_test (x : QM31Exact) :
    field.QM31.is_zero (encode x) = .ok (decide (x = 0)) := by
  have he : x = 0 ↔ x.re = 0 ∧ x.im = 0 := by
    rw [QuadraticAlgebra.ext_iff]; rfl
  simp only [field.QM31.is_zero,R164ProductExecution.encode,cm_zero_test,bind_tc_ok,he]
  by_cases h : x.re = 0 <;> simp [h]
theorem try_inverse_nonzero (x : QM31Exact) (hx : x ≠ 0) :
    field.QM31.try_inv (encode x) = .ok (some (encode x⁻¹)) := by
  have hn := NormInverse.quartic_norm_nonzero x hx
  have hi := cm_inv (NormInverse.quarticNorm x) hn
  have he : (⟨x.re * (NormInverse.quarticNorm x)⁻¹,
      (-x.im) * (NormInverse.quarticNorm x)⁻¹⟩ : QM31Exact) = x⁻¹ := by
    rw [← NormInverse.quartic_inverse_correct x hx]
    simp only [NormInverse.quarticInverse,NormInverse.complex_inverse_correct _ hn]
  simp only [NormInverse.quarticNorm] at hi
  calc
    field.QM31.try_inv (encode x) = .ok (some (encode
        (⟨x.re * (NormInverse.quarticNorm x)⁻¹,
          (-x.im) * (NormInverse.quarticNorm x)⁻¹⟩ : QM31Exact))) := by
      simp only [field.QM31.try_inv,zero_test,hx,decide_false,bind_tc_ok,Bool.false_eq_true,if_false]
      simp only [R164ProductExecution.encode,NormInverse.quarticNorm,cm_square,cm_mul_r,cm_sub,hi,cm_mul,cm_neg,bind_tc_ok]
    _ = .ok (some (encode x⁻¹)) := by rw [he]
theorem try_inverse_zero : field.QM31.try_inv (encode 0) = .ok none := by
  simp only [field.QM31.try_inv,zero_test,decide_true,bind_tc_ok,if_true]
theorem add (x y : QM31Exact) :
    field.QM31.add (encode x) (encode y) = .ok (encode (x+y)) := by
  simp only [field.QM31.add,R164ProductExecution.encode,cm_add,bind_tc_ok,QuadraticAlgebra.re_add,QuadraticAlgebra.im_add]
theorem sub (x y : QM31Exact) :
    field.QM31.sub (encode x) (encode y) = .ok (encode (x-y)) := by
  simp only [field.QM31.sub,R164ProductExecution.encode,cm_sub,bind_tc_ok,QuadraticAlgebra.re_sub,QuadraticAlgebra.im_sub]
theorem square (x : QM31Exact) : field.QM31.square (encode x) = .ok (encode (x*x)) := by
  simp only [field.QM31.square,R164ProductExecution.canonical_product,bind_tc_ok]

theorem one : field.QM31.ONE = encode 1 := by simp only [field.QM31.ONE]; rfl
theorem zero : field.QM31.ZERO = encode 0 := by
  simp only [field.QM31.ZERO]; rfl

def toOldCM (x : field.CM31) : AspisR72Sampler.field.CM31 := ⟨x.a,x.b⟩
def toOld (x : field.QM31) : AspisR72Sampler.field.QM31 := ⟨toOldCM x.c0,toOldCM x.c1⟩
def decode (x : field.QM31) : QM31Exact := SamplerClosureProductCorrectness.decode (toOld x)
def Canonical (x : field.QM31) : Prop := SamplerClosureProductCorrectness.Canonical (toOld x)

theorem toOld_encode (x : QM31Exact) :
    toOld (encode x) = SamplerClosureProductExecution.encode x := rfl

theorem fromOld_toOld (x : field.QM31) : R164ProductExecution.fromOld (toOld x) = x := by
  cases x with
  | mk a b => cases a; cases b; rfl

theorem encode_canonical (x : QM31Exact) : Canonical (encode x) := by
  unfold Canonical
  rw [toOld_encode]
  exact SamplerClosureProductCorrectness.encode_canonical x

theorem decode_encode (x : QM31Exact) : decode (encode x) = x := by
  unfold decode
  rw [toOld_encode]
  exact SamplerClosureProductCorrectness.decode_encode x

theorem encode_decode (x : field.QM31) (hc : Canonical x) : encode (decode x) = x := by
  rw [← R164ProductExecution.encode_same]
  unfold decode
  rw [SamplerClosureProductCorrectness.encode_decode (toOld x) hc,fromOld_toOld]

#print axioms zero_test
#print axioms try_inverse_nonzero
#print axioms try_inverse_zero
#print axioms add
#print axioms sub
#print axioms square
#print axioms one
#print axioms zero
#print axioms toOld_encode
#print axioms fromOld_toOld
#print axioms encode_canonical
#print axioms decode_encode
#print axioms encode_decode
end
end AspisV8R19.R165QuarticExecution

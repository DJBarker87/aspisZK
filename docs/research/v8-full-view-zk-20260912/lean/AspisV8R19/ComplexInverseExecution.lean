import AspisV8R19.ComplexBaseExecution

/-! Source-generated CM31 inverse on canonical word pairs. The norm cannot
vanish for nonzero inputs in the retained exact tower; no nonsquare or inverse
backend premise is introduced here. Zero's assertion failure is retained. -/
set_option autoImplicit false
namespace AspisV8R19.ComplexInverseExecution
open Aeneas Aeneas.Std Result AspisR65Field
open AspisV8R15.ExactTowerBase ComplexBaseExecution
noncomputable section

def encode (x : CM31Exact) : field.CM31 :=
  ⟨encodeBase x.re, encodeBase x.im⟩

def decode (x : field.CM31) : CM31Exact :=
  ⟨(x.a.val : M31Exact), (x.b.val : M31Exact)⟩

def Canonical (x : field.CM31) : Prop := x.a.val < P ∧ x.b.val < P

theorem encode_canonical (x : CM31Exact) : Canonical (encode x) :=
  ⟨ZMod.val_lt x.re, ZMod.val_lt x.im⟩

theorem decode_encode (x : CM31Exact) : decode (encode x) = x := by
  apply QuadraticAlgebra.ext <;> simp only [decode, encode, encodeBase_cast]

theorem encode_decode (x : field.CM31) (hc : Canonical x) : encode (decode x) = x := by
  have ha := eq_encodeBase x.a (x.a.val : M31Exact) hc.1 rfl
  have hb := eq_encodeBase x.b (x.b.val : M31Exact) hc.2 rfl
  cases x
  simp only [encode, decode, ← ha, ← hb]

theorem inverse_encode (x : CM31Exact) (hx : x ≠ 0) :
    field.CM31.inv (encode x) = .ok (encode x⁻¹) := by
  have hn := NormInverse.complex_norm_nonzero x hx
  have hbase := inv_encode (NormInverse.complexNorm x) hn
  have he : (⟨x.re * (NormInverse.complexNorm x)⁻¹,
      (-x.im) * (NormInverse.complexNorm x)⁻¹⟩ : CM31Exact) = x⁻¹ := by
    rw [← NormInverse.complex_inverse_correct x hx]
    simp only [NormInverse.complexInverse, NormInverse.base_inverse_correct _ hn]
  simp only [NormInverse.complexNorm] at hbase
  calc
    field.CM31.inv (encode x) = .ok (encode
        (⟨x.re * (NormInverse.complexNorm x)⁻¹,
          (-x.im) * (NormInverse.complexNorm x)⁻¹⟩ : CM31Exact)) := by
      simp only [field.CM31.inv, field.CM31.inv_with, encode,
        NormInverse.complexNorm, mul_encode, add_encode, hbase, neg_encode, bind_tc_ok]
    _ = .ok (encode x⁻¹) := by rw [he]

theorem inverse_zero : field.CM31.inv (encode 0) = .fail .assertionFailure := by
  simp only [field.CM31.inv, field.CM31.inv_with, encode,
    QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, mul_encode, add_encode,
    zero_mul, zero_add, ComplexBaseExecution.inv_zero, bind_tc_ok, bind_tc_fail]

theorem inverse_execution (x : field.CM31) (hc : Canonical x) :
    field.CM31.inv x =
      if decode x = 0 then .fail .assertionFailure else .ok (encode (decode x)⁻¹) := by
  have he := encode_decode x hc
  by_cases h : decode x = 0
  · rw [if_pos h, ← he, h]
    exact inverse_zero
  · rw [if_neg h]
    conv_lhs => rw [← he]
    exact inverse_encode (decode x) h

theorem inverse_success (x : field.CM31) (hc : Canonical x) (hne : decode x ≠ 0) :
    ∃ y, field.CM31.inv x = .ok y ∧ Canonical y ∧ decode y = (decode x)⁻¹ := by
  refine ⟨encode (decode x)⁻¹, ?_, encode_canonical _, decode_encode _⟩
  rw [inverse_execution x hc, if_neg hne]

theorem zero_iff_limbs (x : field.CM31) (hc : Canonical x) :
    decode x = 0 ↔ x.a.val = 0 ∧ x.b.val = 0 := by
  constructor
  · intro h
    have he := encode_decode x hc
    rw [h] at he
    have ha := congrArg (fun z : field.CM31 => z.a.val) he
    have hb := congrArg (fun z : field.CM31 => z.b.val) he
    exact ⟨ha.symm, hb.symm⟩
  · rintro ⟨ha,hb⟩
    apply QuadraticAlgebra.ext <;> simp [decode, ha, hb]

theorem inverse_failure_iff (x : field.CM31) (hc : Canonical x) :
    field.CM31.inv x = .fail .assertionFailure ↔ x.a.val = 0 ∧ x.b.val = 0 := by
  rw [inverse_execution x hc, ← zero_iff_limbs x hc]
  by_cases h : decode x = 0 <;> simp [h]

theorem entry_execution (x : field.CM31) (hc : Canonical x) :
    complex_inverse_probe x =
      if decode x = 0 then .fail .assertionFailure else .ok (encode (decode x)⁻¹) :=
  inverse_execution x hc

#print axioms encode_canonical
#print axioms decode_encode
#print axioms encode_decode
#print axioms inverse_encode
#print axioms inverse_zero
#print axioms inverse_execution
#print axioms inverse_success
#print axioms zero_iff_limbs
#print axioms inverse_failure_iff
#print axioms entry_execution
end
end AspisV8R19.ComplexInverseExecution

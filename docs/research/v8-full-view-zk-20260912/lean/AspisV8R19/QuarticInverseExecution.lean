import AspisV8R19.LazyComplexExecution

/-! Total generated QM31 try-inverse execution on canonical word tuples.
The norm is proved nonzero from the existing exact tower, not assumed. -/
set_option autoImplicit false
namespace AspisV8R19.QuarticInverseExecution
open Aeneas Aeneas.Std Result AspisR66Field
open AspisV8R15.ExactTowerBase
open ComplexBaseExecution (encodeBase encodeBase_val encodeBase_cast eq_encodeBase)
open LazyComplexExecution (cm_sub cm_neg cm_mul cm_square cm_mul_r cm_inv cm_zero_test)
noncomputable section

def encode (x : QM31Exact) : field.QM31 :=
  ⟨LazyComplexExecution.encode x.re,LazyComplexExecution.encode x.im⟩

def decode (x : field.QM31) : QM31Exact :=
  ⟨⟨(x.c0.a.val : M31Exact),(x.c0.b.val : M31Exact)⟩,
   ⟨(x.c1.a.val : M31Exact),(x.c1.b.val : M31Exact)⟩⟩

def Canonical (x : field.QM31) : Prop :=
  x.c0.a.val < P ∧ x.c0.b.val < P ∧ x.c1.a.val < P ∧ x.c1.b.val < P

theorem encode_canonical (x : QM31Exact) : Canonical (encode x) :=
  ⟨ZMod.val_lt x.re.re,ZMod.val_lt x.re.im,ZMod.val_lt x.im.re,ZMod.val_lt x.im.im⟩

theorem decode_encode (x : QM31Exact) : decode (encode x) = x := by
  apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;>
    simp only [decode,encode,LazyComplexExecution.encode,encodeBase_cast]

theorem encode_decode (x : field.QM31) (hc : Canonical x) : encode (decode x) = x := by
  have ha := eq_encodeBase x.c0.a (x.c0.a.val : M31Exact) hc.1 rfl
  have hb := eq_encodeBase x.c0.b (x.c0.b.val : M31Exact) hc.2.1 rfl
  have hc' := eq_encodeBase x.c1.a (x.c1.a.val : M31Exact) hc.2.2.1 rfl
  have hd := eq_encodeBase x.c1.b (x.c1.b.val : M31Exact) hc.2.2.2 rfl
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  simp only [encode,decode,LazyComplexExecution.encode,← ha,← hb,← hc',← hd]

theorem zero_test (x : QM31Exact) :
    field.QM31.is_zero (encode x) = .ok (decide (x = 0)) := by
  have he : x = 0 ↔ x.re = 0 ∧ x.im = 0 := by
    rw [QuadraticAlgebra.ext_iff]; rfl
  simp only [field.QM31.is_zero,encode,cm_zero_test,bind_tc_ok,he]
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
      simp only [encode,NormInverse.quarticNorm,cm_square,cm_mul_r,cm_sub,hi,cm_mul,cm_neg,bind_tc_ok]
    _ = .ok (some (encode x⁻¹)) := by rw [he]

theorem try_inverse_zero : field.QM31.try_inv (encode 0) = .ok none := by
  simp only [field.QM31.try_inv,zero_test,decide_true,bind_tc_ok,if_true]

theorem try_inverse_execution (x : field.QM31) (hc : Canonical x) :
    field.QM31.try_inv x = .ok
      (if decode x = 0 then none else some (encode (decode x)⁻¹)) := by
  have he := encode_decode x hc
  by_cases h : decode x = 0
  · rw [if_pos h,← he,h]
    exact try_inverse_zero
  · rw [if_neg h]
    conv_lhs => rw [← he]
    exact try_inverse_nonzero (decode x) h

theorem zero_iff_limbs (x : field.QM31) (hc : Canonical x) :
    decode x = 0 ↔ x.c0.a.val = 0 ∧ x.c0.b.val = 0 ∧ x.c1.a.val = 0 ∧ x.c1.b.val = 0 := by
  constructor
  · intro h
    have he := encode_decode x hc
    rw [h] at he
    exact ⟨(congrArg (fun z : field.QM31 => z.c0.a.val) he).symm,
      (congrArg (fun z : field.QM31 => z.c0.b.val) he).symm,
      (congrArg (fun z : field.QM31 => z.c1.a.val) he).symm,
      (congrArg (fun z : field.QM31 => z.c1.b.val) he).symm⟩
  · rintro ⟨ha,hb,hc',hd⟩
    apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;> simp [decode,ha,hb,hc',hd]

theorem none_iff_zero (x : field.QM31) (hc : Canonical x) :
    field.QM31.try_inv x = .ok none ↔
      x.c0.a.val = 0 ∧ x.c0.b.val = 0 ∧ x.c1.a.val = 0 ∧ x.c1.b.val = 0 := by
  rw [try_inverse_execution x hc,← zero_iff_limbs x hc]
  by_cases h : decode x = 0 <;> simp [h]

theorem some_inverse (x : field.QM31) (hc : Canonical x) (hx : decode x ≠ 0) :
    ∃ y, field.QM31.try_inv x = .ok (some y) ∧ Canonical y ∧ decode y = (decode x)⁻¹ := by
  refine ⟨encode (decode x)⁻¹,?_,encode_canonical _,decode_encode _⟩
  rw [try_inverse_execution x hc,if_neg hx]

theorem no_failure (x : field.QM31) (hc : Canonical x) (e : Error) :
    field.QM31.try_inv x ≠ .fail e := by
  rw [try_inverse_execution x hc]
  simp

theorem entry_execution (x : field.QM31) (hc : Canonical x) :
    quartic_inverse_probe x = .ok
      (if decode x = 0 then none else some (encode (decode x)⁻¹)) :=
  try_inverse_execution x hc

theorem retained_model_correspondence (x : field.QM31) (hc : Canonical x) :
    (do
      let out ← field.QM31.try_inv x
      ok (out.map decode)) = .ok (NormInverse.tryInverse (decode x)) := by
  rw [try_inverse_execution x hc]
  by_cases h : decode x = 0
  · simp [h,NormInverse.tryInverse]
  · simp [h,NormInverse.tryInverse,decode_encode,NormInverse.quartic_inverse_correct _ h]

#print axioms encode_canonical
#print axioms decode_encode
#print axioms encode_decode
#print axioms zero_test
#print axioms try_inverse_nonzero
#print axioms try_inverse_zero
#print axioms try_inverse_execution
#print axioms zero_iff_limbs
#print axioms none_iff_zero
#print axioms some_inverse
#print axioms no_failure
#print axioms entry_execution
#print axioms retained_model_correspondence
end
end AspisV8R19.QuarticInverseExecution

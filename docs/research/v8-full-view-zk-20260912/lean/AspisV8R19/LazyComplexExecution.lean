import AspisV8R19.QuarticBaseExecution

/-! Word-level bounds and execution of the selected raw-representative CM31
multiplication/square, followed by exact tower algebra. -/
set_option autoImplicit false
namespace AspisV8R19.LazyComplexExecution
open Aeneas Aeneas.Std Result AspisR66Field
open AspisV8R15.ExactTowerBase QuarticBaseExecution
open ComplexBaseExecution (encodeBase encodeBase_val encodeBase_cast)
noncomputable section

def encode (x : CM31Exact) : field.CM31 := ⟨encodeBase x.re,encodeBase x.im⟩

abbrev wide (x : M31Exact) : U64 := core.convert.num.FromU64U32.from (encodeBase x)

theorem wide_value (x : M31Exact) : (wide x).val = x.val := by
  rw [from_value,encodeBase_val]

theorem raw_sum (x y : M31Exact) :
    ∃ s : U64, (wide x + wide y : Result U64) = .ok s ∧
      s.val = x.val+y.val ∧ s.val < 2^32 := by
  have hx := ZMod.val_lt x
  have hy := ZMod.val_lt y
  have hb : (wide x).val+(wide y).val < 2^64 := by
    rw [wide_value,wide_value]; unfold P at *; omega
  obtain ⟨s,hs,hv⟩ := InverseRuntimeMul.add_success _ _ hb
  rw [wide_value,wide_value] at hv
  exact ⟨s,hs,hv,by rw [hv]; unfold P at *; omega⟩

theorem raw_difference (x y : M31Exact) :
    ∃ a s : U64,
      (wide x + core.convert.num.FromU64U32.from field.P : Result U64) = .ok a ∧
      (a - wide y : Result U64) = .ok s ∧
      s.val = x.val+P-y.val ∧ s.val < 2^32 := by
  have hx := ZMod.val_lt x
  have hy := ZMod.val_lt y
  have hp : (core.convert.num.FromU64U32.from field.P).val = P := by
    rw [from_value]; simp [field.P,P]
  obtain ⟨a,ha,hav⟩ := InverseRuntimeMul.add_success (wide x)
    (core.convert.num.FromU64U32.from field.P) (by rw [wide_value,hp]; unfold P at *; omega)
  rw [wide_value,hp] at hav
  obtain ⟨s,hs,hsv⟩ := InverseRuntimeMul.sub_success a (wide y) (by rw [hav,wide_value]; omega)
  rw [hav,wide_value] at hsv
  exact ⟨a,s,ha,hs,hsv,by rw [hsv]; unfold P at *; omega⟩

theorem raw_product (s t : U64) (hs : s.val < 2^32) (ht : t.val < 2^32) :
    ∃ p : U64, field.r23_product_u32_bounded s t = .ok p ∧
      field.M31.reduce_u64 p = .ok (encodeBase ((s.val : M31Exact)*(t.val : M31Exact))) := by
  obtain ⟨p,hp,hpv⟩ := width_product s t hs ht
  refine ⟨p,hp,?_⟩
  rw [reduce_encode,hpv,Nat.cast_mul]

theorem cm_sub (x y : CM31Exact) :
    field.CM31.sub (encode x) (encode y) = .ok (encode (x-y)) := by
  simp only [field.CM31.sub,encode,sub_encode,bind_tc_ok,
    QuadraticAlgebra.re_sub,QuadraticAlgebra.im_sub]

theorem cm_neg (x : CM31Exact) : field.CM31.neg (encode x) = .ok (encode (-x)) := by
  simp only [field.CM31.neg,encode,neg_encode,bind_tc_ok,
    QuadraticAlgebra.re_neg,QuadraticAlgebra.im_neg]

theorem cm_mul (x y : CM31Exact) :
    field.CM31.mul (encode x) (encode y) = .ok (encode (x*y)) := by
  obtain ⟨s,hs,hsv,hsb⟩ := raw_sum x.re x.im
  obtain ⟨t,ht,htv,htb⟩ := raw_sum y.re y.im
  obtain ⟨p,hp,hpr⟩ := raw_product s t hsb htb
  rw [hsv,htv,Nat.cast_add,Nat.cast_add,ZMod.natCast_zmod_val,
    ZMod.natCast_zmod_val,ZMod.natCast_zmod_val,ZMod.natCast_zmod_val] at hpr
  have he : (⟨x.re*y.re-x.im*y.im,
      (x.re+x.im)*(y.re+y.im)-x.re*y.re-x.im*y.im⟩ : CM31Exact) = x*y := by
    apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul] <;> ring
  calc
    field.CM31.mul (encode x) (encode y) = .ok (encode
        (⟨x.re*y.re-x.im*y.im,
          (x.re+x.im)*(y.re+y.im)-x.re*y.re-x.im*y.im⟩ : CM31Exact)) := by
      simp only [field.CM31.mul,encode,mul_encode,lift,bind_tc_ok,hs,ht,hp,hpr,sub_encode]
    _ = .ok (encode (x*y)) := by rw [he]

theorem cm_square (x : CM31Exact) : field.CM31.square (encode x) = .ok (encode (x*x)) := by
  obtain ⟨s,hs,hsv,hsb⟩ := raw_sum x.re x.im
  obtain ⟨a,t,ha,ht,htv,htb⟩ := raw_difference x.re x.im
  obtain ⟨p,hp,hpr⟩ := raw_product s t hsb htb
  have hi := ZMod.val_lt x.im
  have hn : x.im.val ≤ x.re.val+P := by omega
  have hcast : (t.val : M31Exact) = x.re-x.im := by
    rw [htv,Nat.cast_sub hn,Nat.cast_add,ZMod.natCast_zmod_val,ZMod.natCast_zmod_val]
    simp [P,M31Exact]
  rw [hsv,Nat.cast_add,ZMod.natCast_zmod_val,ZMod.natCast_zmod_val,hcast] at hpr
  have he : (⟨(x.re+x.im)*(x.re-x.im),x.re*x.im+x.re*x.im⟩ : CM31Exact) = x*x := by
    apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul] <;> ring
  calc
    field.CM31.square (encode x) = .ok (encode
        (⟨(x.re+x.im)*(x.re-x.im),x.re*x.im+x.re*x.im⟩ : CM31Exact)) := by
      simp only [field.CM31.square,encode,lift,bind_tc_ok,hs,ha,ht,hp,hpr,mul_encode,double_encode]
    _ = .ok (encode (x*x)) := by rw [he]

theorem cm_mul_r (x : CM31Exact) : field.mul_by_r (encode x) = .ok (encode (qm31R*x)) := by
  have he : (⟨x.re+x.re-x.im,x.re+(x.im+x.im)⟩ : CM31Exact) = qm31R*x := by
    apply QuadraticAlgebra.ext <;> simp [qm31R,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul] <;> ring
  calc
    field.mul_by_r (encode x) = .ok (encode (⟨x.re+x.re-x.im,x.re+(x.im+x.im)⟩ : CM31Exact)) := by
      simp only [field.mul_by_r,encode,double_encode,sub_encode,add_encode,bind_tc_ok]
    _ = .ok (encode (qm31R*x)) := by rw [he]

theorem cm_inv (x : CM31Exact) (hx : x ≠ 0) :
    field.CM31.inv (encode x) = .ok (encode x⁻¹) := by
  have hn := NormInverse.complex_norm_nonzero x hx
  have hbase := inv_encode (NormInverse.complexNorm x) hn
  have he : (⟨x.re * (NormInverse.complexNorm x)⁻¹,
      (-x.im) * (NormInverse.complexNorm x)⁻¹⟩ : CM31Exact) = x⁻¹ := by
    rw [← NormInverse.complex_inverse_correct x hx]
    simp only [NormInverse.complexInverse,NormInverse.base_inverse_correct _ hn]
  simp only [NormInverse.complexNorm] at hbase
  calc
    field.CM31.inv (encode x) = .ok (encode
        (⟨x.re * (NormInverse.complexNorm x)⁻¹,
          (-x.im) * (NormInverse.complexNorm x)⁻¹⟩ : CM31Exact)) := by
      simp only [field.CM31.inv,field.CM31.inv_with,encode,
        NormInverse.complexNorm,mul_encode,add_encode,hbase,neg_encode,bind_tc_ok]
    _ = .ok (encode x⁻¹) := by rw [he]

theorem cm_zero_test (x : CM31Exact) :
    field.CM31.is_zero (encode x) = .ok (decide (x = 0)) := by
  have he : x = 0 ↔ x.re = 0 ∧ x.im = 0 := by
    rw [QuadraticAlgebra.ext_iff]; rfl
  simp only [field.CM31.is_zero,encode,base_zero_test,bind_tc_ok,he]
  by_cases h : x.re = 0 <;> simp [h]

#print axioms wide_value
#print axioms raw_sum
#print axioms raw_difference
#print axioms raw_product
#print axioms cm_sub
#print axioms cm_neg
#print axioms cm_mul
#print axioms cm_square
#print axioms cm_mul_r
#print axioms cm_inv
#print axioms cm_zero_test
end
end AspisV8R19.LazyComplexExecution

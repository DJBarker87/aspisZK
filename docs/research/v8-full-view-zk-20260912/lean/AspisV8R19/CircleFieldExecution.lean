import AspisV8R19.CircleScalarTransport

/-! Reuse the R66 raw bounds and inverse algebra for the R69 source closure. -/
set_option autoImplicit false
namespace AspisV8R19.CircleFieldExecution
open Aeneas Aeneas.Std Result AspisR69Explicit CircleScalarTransport
open AspisV8R15.ExactTowerBase
open ProductExecution (encode encodeCM)
open ComplexBaseExecution (encodeBase)
noncomputable section

theorem cm_add (x y : CM31Exact) :
    field.CM31.add (encodeCM x) (encodeCM y) = .ok (encodeCM (x+y)) := by
  simp only [field.CM31.add,encodeCM,add_encode,bind_tc_ok,
    QuadraticAlgebra.re_add,QuadraticAlgebra.im_add]
theorem cm_sub (x y : CM31Exact) :
    field.CM31.sub (encodeCM x) (encodeCM y) = .ok (encodeCM (x-y)) := by
  simp only [field.CM31.sub,encodeCM,sub_encode,bind_tc_ok,
    QuadraticAlgebra.re_sub,QuadraticAlgebra.im_sub]
theorem cm_neg (x : CM31Exact) : field.CM31.neg (encodeCM x) = .ok (encodeCM (-x)) := by
  simp only [field.CM31.neg,encodeCM,neg_encode,bind_tc_ok,
    QuadraticAlgebra.re_neg,QuadraticAlgebra.im_neg]
theorem cm_mul (x y : CM31Exact) :
    field.CM31.mul (encodeCM x) (encodeCM y) = .ok (encodeCM (x*y)) := by
  obtain ⟨s,hs,hsv,hsb⟩ := LazyComplexExecution.raw_sum x.re x.im
  obtain ⟨t,ht,htv,htb⟩ := LazyComplexExecution.raw_sum y.re y.im
  obtain ⟨p,hp,hpr⟩ := raw_product s t hsb htb
  rw [hsv,htv,Nat.cast_add,Nat.cast_add,ZMod.natCast_zmod_val,
    ZMod.natCast_zmod_val,ZMod.natCast_zmod_val,ZMod.natCast_zmod_val] at hpr
  have he : (⟨x.re*y.re-x.im*y.im,
      (x.re+x.im)*(y.re+y.im)-x.re*y.re-x.im*y.im⟩ : CM31Exact) = x*y := by
    apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul] <;> ring
  calc
    field.CM31.mul (encodeCM x) (encodeCM y) = .ok (encodeCM
        (⟨x.re*y.re-x.im*y.im,
          (x.re+x.im)*(y.re+y.im)-x.re*y.re-x.im*y.im⟩ : CM31Exact)) := by
      simp only [field.CM31.mul,encodeCM,mul_encode,lift,bind_tc_ok,hs,ht,hp,hpr,sub_encode]
    _ = .ok (encodeCM (x*y)) := by rw [he]
theorem cm_square (x : CM31Exact) : field.CM31.square (encodeCM x) = .ok (encodeCM (x*x)) := by
  obtain ⟨s,hs,hsv,hsb⟩ := LazyComplexExecution.raw_sum x.re x.im
  obtain ⟨a,t,ha,ht,htv,htb⟩ := LazyComplexExecution.raw_difference x.re x.im
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
    field.CM31.square (encodeCM x) = .ok (encodeCM
        (⟨(x.re+x.im)*(x.re-x.im),x.re*x.im+x.re*x.im⟩ : CM31Exact)) := by
      simp only [field.CM31.square,encodeCM,lift,bind_tc_ok,prime_eq,hs,ha,ht,hp,hpr,mul_encode,double_encode]
    _ = .ok (encodeCM (x*x)) := by rw [he]
theorem cm_mul_r (x : CM31Exact) : field.mul_by_r (encodeCM x) = .ok (encodeCM (qm31R*x)) := by
  have he : (⟨x.re+x.re-x.im,x.re+(x.im+x.im)⟩ : CM31Exact) = qm31R*x := by
    apply QuadraticAlgebra.ext <;> simp [qm31R,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul] <;> ring
  calc
    field.mul_by_r (encodeCM x) = .ok (encodeCM (⟨x.re+x.re-x.im,x.re+(x.im+x.im)⟩ : CM31Exact)) := by
      simp only [field.mul_by_r,encodeCM,double_encode,sub_encode,add_encode,bind_tc_ok]
    _ = .ok (encodeCM (qm31R*x)) := by rw [he]
theorem cm_inv (x : CM31Exact) (hx : x ≠ 0) :
    field.CM31.inv (encodeCM x) = .ok (encodeCM x⁻¹) := by
  have hn := NormInverse.complex_norm_nonzero x hx
  have hbase := inv_encode (NormInverse.complexNorm x) hn
  have he : (⟨x.re * (NormInverse.complexNorm x)⁻¹,
      (-x.im) * (NormInverse.complexNorm x)⁻¹⟩ : CM31Exact) = x⁻¹ := by
    rw [← NormInverse.complex_inverse_correct x hx]
    simp only [NormInverse.complexInverse,NormInverse.base_inverse_correct _ hn]
  simp only [NormInverse.complexNorm] at hbase
  calc
    field.CM31.inv (encodeCM x) = .ok (encodeCM
        (⟨x.re * (NormInverse.complexNorm x)⁻¹,
          (-x.im) * (NormInverse.complexNorm x)⁻¹⟩ : CM31Exact)) := by
      simp only [field.CM31.inv,field.CM31.inv_with,encodeCM,
        NormInverse.complexNorm,mul_encode,add_encode,hbase,neg_encode,bind_tc_ok]
    _ = .ok (encodeCM x⁻¹) := by rw [he]
theorem cm_zero_test (x : CM31Exact) :
    field.CM31.is_zero (encodeCM x) = .ok (decide (x = 0)) := by
  have he : x = 0 ↔ x.re = 0 ∧ x.im = 0 := by
    rw [QuadraticAlgebra.ext_iff]; rfl
  simp only [field.CM31.is_zero,encodeCM,base_zero_test,bind_tc_ok,he]
  by_cases h : x.re = 0 <;> simp [h]
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
theorem add (x y : QM31Exact) :
    field.QM31.add (encode x) (encode y) = .ok (encode (x+y)) := by
  simp only [field.QM31.add,encode,cm_add,bind_tc_ok,QuadraticAlgebra.re_add,QuadraticAlgebra.im_add]
theorem sub (x y : QM31Exact) :
    field.QM31.sub (encode x) (encode y) = .ok (encode (x-y)) := by
  simp only [field.QM31.sub,encode,cm_sub,bind_tc_ok,QuadraticAlgebra.re_sub,QuadraticAlgebra.im_sub]
theorem square (x : QM31Exact) : field.QM31.square (encode x) = .ok (encode (x*x)) := by
  have he : (⟨x.re*x.re+qm31R*(x.im*x.im),x.re*x.im+x.re*x.im⟩ : QM31Exact) = x*x := by
    apply QuadraticAlgebra.ext <;>
      simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul] <;> ring
  calc
    field.QM31.square (encode x) = .ok (encode
        (⟨x.re*x.re+qm31R*(x.im*x.im),x.re*x.im+x.re*x.im⟩ : QM31Exact)) := by
      simp only [field.QM31.square,encode,cm_square,cm_mul_r,cm_add,cm_mul,
        field.CM31.double,bind_tc_ok]
    _ = .ok (encode (x*x)) := by rw [he]
theorem one : field.QM31.ONE = encode 1 := by simp only [field.QM31.ONE]; rfl

#print axioms cm_add
#print axioms cm_sub
#print axioms cm_neg
#print axioms cm_mul
#print axioms cm_square
#print axioms cm_mul_r
#print axioms cm_inv
#print axioms cm_zero_test
#print axioms zero_test
#print axioms try_inverse_nonzero
#print axioms try_inverse_zero
#print axioms add
#print axioms sub
#print axioms square
#print axioms one
end
end AspisV8R19.CircleFieldExecution

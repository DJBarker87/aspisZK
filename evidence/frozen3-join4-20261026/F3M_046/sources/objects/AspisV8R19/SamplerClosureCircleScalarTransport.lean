/- Mechanically reused R70/R71 proof script for the actual R72 closure.
Only identifier renaming and removal of the absent diagnostic-probe corollary.
Checked by tools/generate_r78_closure.py; original files are preserved. -/
import AspisV8R19.SamplerClosureProductCorrectness
import AspisV8R19.QuarticInverseExecution

/-! Definitional source transport; no new arithmetic backend premise. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerClosureCircleScalarTransport
open Aeneas Aeneas.Std Result AspisR72Sampler
open AspisV8R15.ExactTowerBase
open ComplexBaseExecution (encodeBase)

theorem prime_eq : field.P = AspisR66Field.field.P := by
  simp only [field.P,AspisR66Field.field.P]
theorem reducer_eq (x : U64) : field.reduce_u64 x = AspisR66Field.field.reduce_u64 x := by
  simp only [field.reduce_u64,AspisR66Field.field.reduce_u64,prime_eq]
theorem mul_eq (x y : U32) : field.M31.mul x y = AspisR66Field.field.M31.mul x y := by
  simp only [field.M31.mul,AspisR66Field.field.M31.mul,prime_eq,reducer_eq]
theorem body_eq (r : core.ops.range.Range Usize) (x : U32) :
    field.square_n_loop.body r x = AspisR66Field.field.square_n_loop.body r x := by
  simp only [field.square_n_loop.body,AspisR66Field.field.square_n_loop.body,mul_eq]
  rfl
theorem loop_eq (r : core.ops.range.Range Usize) (x : U32) :
    field.square_n_loop r x = AspisR66Field.field.square_n_loop r x := by
  simp only [field.square_n_loop,AspisR66Field.field.square_n_loop,body_eq]
theorem square_eq (x : U32) (n : Usize) :
    field.square_n x n = AspisR66Field.field.square_n x n := by
  simp only [field.square_n,AspisR66Field.field.square_n,loop_eq]
theorem inv_eq (x : U32) : field.M31.inv x = AspisR66Field.field.M31.inv x := by
  simp only [field.M31.inv,AspisR66Field.field.M31.inv,mul_eq,square_eq]
theorem add_eq (x y : U32) : field.M31.add x y = AspisR66Field.field.M31.add x y := by
  simp only [field.M31.add,AspisR66Field.field.M31.add,prime_eq]
theorem sub_eq (x y : U32) : field.M31.sub x y = AspisR66Field.field.M31.sub x y := by
  simp only [field.M31.sub,AspisR66Field.field.M31.sub,prime_eq]
theorem neg_eq (x : U32) : field.M31.neg x = AspisR66Field.field.M31.neg x := by
  simp only [field.M31.neg,AspisR66Field.field.M31.neg,prime_eq]
theorem reduce_eq (x : U64) :
    field.M31.reduce_u64 x = AspisR66Field.field.M31.reduce_u64 x := by
  simp only [field.M31.reduce_u64,AspisR66Field.field.M31.reduce_u64,reducer_eq]
theorem width_eq (x y : U64) :
    field.r23_product_u32_bounded x y = AspisR66Field.field.r23_product_u32_bounded x y := rfl

theorem mul_encode (x y : M31Exact) :
    field.M31.mul (encodeBase x) (encodeBase y) = .ok (encodeBase (x*y)) := by
  rw [mul_eq]; exact QuarticBaseExecution.mul_encode x y
theorem add_encode (x y : M31Exact) :
    field.M31.add (encodeBase x) (encodeBase y) = .ok (encodeBase (x+y)) := by
  rw [add_eq]; exact QuarticBaseExecution.add_encode x y
theorem sub_encode (x y : M31Exact) :
    field.M31.sub (encodeBase x) (encodeBase y) = .ok (encodeBase (x-y)) := by
  rw [sub_eq]; exact QuarticBaseExecution.sub_encode x y
theorem neg_encode (x : M31Exact) : field.M31.neg (encodeBase x) = .ok (encodeBase (-x)) := by
  rw [neg_eq]; exact QuarticBaseExecution.neg_encode x
theorem double_encode (x : M31Exact) :
    field.M31.double (encodeBase x) = .ok (encodeBase (x+x)) := add_encode x x
theorem inv_encode (x : M31Exact) (hx : x ≠ 0) :
    field.M31.inv (encodeBase x) = .ok (encodeBase x⁻¹) := by
  rw [inv_eq]; exact QuarticBaseExecution.inv_encode x hx
theorem base_zero_test (x : M31Exact) :
    field.M31.is_zero (encodeBase x) = .ok (decide (x = 0)) :=
  QuarticBaseExecution.base_zero_test x
theorem raw_product (s t : U64) (hs : s.val < 2^32) (ht : t.val < 2^32) :
    ∃ p : U64, field.r23_product_u32_bounded s t = .ok p ∧
      field.M31.reduce_u64 p = .ok (encodeBase ((s.val : M31Exact)*(t.val : M31Exact))) := by
  simp only [width_eq,reduce_eq]
  exact LazyComplexExecution.raw_product s t hs ht

#print axioms prime_eq
#print axioms reducer_eq
#print axioms mul_eq
#print axioms body_eq
#print axioms loop_eq
#print axioms square_eq
#print axioms inv_eq
#print axioms add_eq
#print axioms sub_eq
#print axioms neg_eq
#print axioms reduce_eq
#print axioms width_eq
#print axioms mul_encode
#print axioms add_encode
#print axioms sub_encode
#print axioms neg_encode
#print axioms double_encode
#print axioms inv_encode
#print axioms base_zero_test
#print axioms raw_product
end AspisV8R19.SamplerClosureCircleScalarTransport

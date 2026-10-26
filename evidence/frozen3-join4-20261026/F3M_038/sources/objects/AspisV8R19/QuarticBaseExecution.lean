import AspisV8R19.QuarticFieldSlice
import AspisV8R19.ComplexInverseExecution

/-! Checked word operations used by the actual lazy/raw CM31 kernels. -/
set_option autoImplicit false
namespace AspisV8R19.QuarticBaseExecution
open Aeneas Aeneas.Std Result AspisR66Field
open AspisV8R15.ExactTowerBase
open ComplexBaseExecution (encodeBase encodeBase_val encodeBase_cast eq_encodeBase)

theorem reducer_eq (x : U64) : field.reduce_u64 x = AspisR65Field.field.reduce_u64 x := by
  simp only [field.reduce_u64, AspisR65Field.field.reduce_u64, field.P, AspisR65Field.field.P]

theorem mul_eq (x y : U32) : field.M31.mul x y = AspisR65Field.field.M31.mul x y := by
  simp only [field.M31.mul, AspisR65Field.field.M31.mul, field.P, AspisR65Field.field.P, reducer_eq]

theorem body_eq (r : core.ops.range.Range Usize) (x : U32) :
    field.square_n_loop.body r x = AspisR65Field.field.square_n_loop.body r x := by
  simp only [field.square_n_loop.body, AspisR65Field.field.square_n_loop.body, mul_eq]
  rfl

theorem loop_eq (r : core.ops.range.Range Usize) (x : U32) :
    field.square_n_loop r x = AspisR65Field.field.square_n_loop r x := by
  simp only [field.square_n_loop, AspisR65Field.field.square_n_loop, body_eq]

theorem square_eq (x : U32) (n : Usize) : field.square_n x n = AspisR65Field.field.square_n x n := by
  simp only [field.square_n, AspisR65Field.field.square_n, loop_eq]

theorem inv_eq (x : U32) : field.M31.inv x = AspisR65Field.field.M31.inv x := by
  simp only [field.M31.inv, AspisR65Field.field.M31.inv, mul_eq, square_eq]

theorem add_eq (x y : U32) : field.M31.add x y = AspisR65Field.field.M31.add x y := by
  simp only [field.M31.add, AspisR65Field.field.M31.add, field.P, AspisR65Field.field.P]

theorem neg_eq (x : U32) : field.M31.neg x = AspisR65Field.field.M31.neg x := by
  simp only [field.M31.neg, AspisR65Field.field.M31.neg, field.P, AspisR65Field.field.P]

theorem mul_encode (x y : M31Exact) :
    field.M31.mul (encodeBase x) (encodeBase y) = .ok (encodeBase (x*y)) := by
  rw [mul_eq]; exact ComplexBaseExecution.mul_encode x y

theorem add_encode (x y : M31Exact) :
    field.M31.add (encodeBase x) (encodeBase y) = .ok (encodeBase (x+y)) := by
  rw [add_eq]; exact ComplexBaseExecution.add_encode x y

theorem neg_encode (x : M31Exact) : field.M31.neg (encodeBase x) = .ok (encodeBase (-x)) := by
  rw [neg_eq]; exact ComplexBaseExecution.neg_encode x

theorem inv_encode (x : M31Exact) (hx : x ≠ 0) :
    field.M31.inv (encodeBase x) = .ok (encodeBase x⁻¹) := by
  rw [inv_eq]; exact ComplexBaseExecution.inv_encode x hx

theorem double_encode (x : M31Exact) :
    field.M31.double (encodeBase x) = .ok (encodeBase (x+x)) := add_encode x x

def finish32 (s : U32) : Result U32 := do
  if s >= field.P then
    let z ← s - field.P
    ok z
  else ok s

theorem finish_success (s : U32) (hs : s.val < 2*P) :
    ∃ z : U32, finish32 s = .ok z ∧ z.val = s.val%P ∧ z.val < P := by
  have hp : field.P.val = P := by simp [field.P, P]
  by_cases h : P ≤ s.val
  · obtain ⟨z, hz, hv⟩ := InverseRuntimeMul.sub_success s field.P (by simpa only [hp] using h)
    change (s - field.P : Result U32) = .ok z at hz
    have hc : z.val < P := by rw [hv,hp]; omega
    refine ⟨z, ?_, ?_, hc⟩
    · simp only [finish32, UScalar.le_equiv, hp, h, if_true, hz, bind_tc_ok]
    · rw [hv,hp,Nat.mod_eq_sub_mod h,Nat.mod_eq_of_lt (by omega)]
  · refine ⟨s, ?_, ?_, by omega⟩
    · simp only [finish32, UScalar.le_equiv, hp, h, if_false]
    · rw [Nat.mod_eq_of_lt (by omega)]

theorem sub_encode (x y : M31Exact) :
    field.M31.sub (encodeBase x) (encodeBase y) = .ok (encodeBase (x-y)) := by
  have hx := ZMod.val_lt x
  have hy := ZMod.val_lt y
  have hp : field.P.val = P := by simp [field.P, P]
  have hb : (encodeBase x).val + field.P.val < 2^32 := by
    rw [encodeBase_val,hp]; unfold P at *; omega
  obtain ⟨a,ha,hav⟩ := InverseRuntimeMul.tryMk_success (ty := .U32) _ hb
  change (encodeBase x + field.P : Result U32) = .ok a at ha
  obtain ⟨s,hs,hsv⟩ := InverseRuntimeMul.sub_success a (encodeBase y) (by
    rw [hav,encodeBase_val,encodeBase_val,hp]; omega)
  change (a - encodeBase y : Result U32) = .ok s at hs
  have hsb : s.val < 2*P := by rw [hsv,hav,hp,encodeBase_val,encodeBase_val]; omega
  obtain ⟨z,hz,hzv,hzc⟩ := finish_success s hsb
  have he : z = encodeBase (x-y) := by
    apply eq_encodeBase z (x-y) hzc
    rw [hzv,ZMod.natCast_mod,hsv,hav,hp,encodeBase_val,encodeBase_val]
    rw [Nat.cast_sub (by omega),Nat.cast_add,ZMod.natCast_zmod_val,ZMod.natCast_zmod_val]
    simp [P,M31Exact]
  simp only [field.M31.sub,ha,hs,bind_tc_ok]
  change finish32 s = .ok (encodeBase (x-y))
  rw [hz,he]

theorem reduce_encode (x : U64) :
    field.M31.reduce_u64 x = .ok (encodeBase (x.val : M31Exact)) := by
  obtain ⟨z,hz,hv,hc⟩ := InverseRuntimeMul.generated_reducer_mod x
  have hr : field.reduce_u64 x = .ok z := by
    rw [reducer_eq,ComplexBaseExecution.reducer_eq,GuardedM31Execution.reducer_eq]
    exact hz
  simp only [field.M31.reduce_u64,hr,bind_tc_ok]
  congr 1
  apply eq_encodeBase z (x.val : M31Exact) hc
  rw [hv,ZMod.natCast_mod]

theorem from_value (x : U32) : (core.convert.num.FromU64U32.from x).val = x.val :=
  core.convert.num.FromU64U32.from_val_eq x

theorem width_roundtrip (x : U64) (hx : x.val < 2^32) :
    core.convert.num.FromU64U32.from (UScalar.cast .U32 x) = x := by
  apply UScalar.eq_of_val_eq
  rw [from_value,InverseRuntimeMul.narrow_exact x hx]

theorem width_product (x y : U64) (hx : x.val < 2^32) (hy : y.val < 2^32) :
    ∃ z : U64, field.r23_product_u32_bounded x y = .ok z ∧ z.val = x.val*y.val := by
  have hmax : (core.convert.num.FromU64U32.from core.num.U32.MAX).val = 2^32-1 := rfl
  have ha : x ≤ core.convert.num.FromU64U32.from core.num.U32.MAX := by
    rw [UScalar.le_equiv,hmax]; omega
  have hb : y ≤ core.convert.num.FromU64U32.from core.num.U32.MAX := by
    rw [UScalar.le_equiv,hmax]; omega
  have hprod : x.val*y.val < 2^64 := by
    have h := Nat.mul_lt_mul_of_lt_of_lt hx hy
    exact h
  obtain ⟨z,hz,hv⟩ := InverseRuntimeMul.mul_success x y hprod
  change (x * y : Result U64) = .ok z at hz
  refine ⟨z, ?_, hv⟩
  simp only [field.r23_product_u32_bounded,lift,bind_tc_ok,ha,hb,if_true,
    width_roundtrip x hx,width_roundtrip y hy,hz]

theorem base_zero_test (x : M31Exact) :
    field.M31.is_zero (encodeBase x) = .ok (decide (x = 0)) := by
  have he : encodeBase x = 0#u32 ↔ x = 0 := by
    constructor
    · intro h
      have v := encodeBase_cast x
      rw [h] at v
      exact v.symm
    · intro h; subst x; rfl
  simp only [field.M31.is_zero,he]

#print axioms reducer_eq
#print axioms mul_eq
#print axioms body_eq
#print axioms loop_eq
#print axioms square_eq
#print axioms inv_eq
#print axioms add_eq
#print axioms neg_eq
#print axioms mul_encode
#print axioms add_encode
#print axioms neg_encode
#print axioms inv_encode
#print axioms double_encode
#print axioms finish_success
#print axioms sub_encode
#print axioms reduce_encode
#print axioms from_value
#print axioms width_roundtrip
#print axioms width_product
#print axioms base_zero_test
end AspisV8R19.QuarticBaseExecution

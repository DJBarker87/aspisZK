import AspisV8R19.ComplexFieldSlice
import AspisV8R19.GuardedInverseExecution
import AspisV8R19.NormInverse

/-! The freshly extracted CM31 closure reuses the checked M31 execution.
Addition and negation are proved only on canonical inputs, as required by
the field representation; the predicates are not assumed for untrusted bytes. -/
set_option autoImplicit false
namespace AspisV8R19.ComplexBaseExecution
open Aeneas Aeneas.Std Result AspisR65Field
open AspisV8R15.ExactTowerBase

theorem reducer_eq (x : U64) :
    field.reduce_u64 x = AspisR64Field.field.reduce_u64 x := by
  simp only [field.reduce_u64, AspisR64Field.field.reduce_u64,
    field.P, AspisR64Field.field.P]

theorem mul_eq (x y : U32) :
    field.M31.mul x y = AspisR64Field.field.M31.mul x y := by
  simp only [field.M31.mul, AspisR64Field.field.M31.mul,
    field.P, AspisR64Field.field.P, reducer_eq]

theorem body_eq (r : core.ops.range.Range Usize) (x : U32) :
    field.square_n_loop.body r x = AspisR64Field.field.square_n_loop.body r x := by
  simp only [field.square_n_loop.body, AspisR64Field.field.square_n_loop.body, mul_eq]
  rfl

theorem loop_eq (r : core.ops.range.Range Usize) (x : U32) :
    field.square_n_loop r x = AspisR64Field.field.square_n_loop r x := by
  simp only [field.square_n_loop, AspisR64Field.field.square_n_loop, body_eq]

theorem square_eq (x : U32) (n : Usize) :
    field.square_n x n = AspisR64Field.field.square_n x n := by
  simp only [field.square_n, AspisR64Field.field.square_n, loop_eq]

theorem inv_eq (x : U32) : field.M31.inv x = AspisR64Field.field.M31.inv x := by
  simp only [field.M31.inv, AspisR64Field.field.M31.inv, mul_eq, square_eq]

def encodeBase (x : M31Exact) : U32 :=
  GeneratedInverseLoop.encode ⟨x.val, ZMod.val_lt x⟩

@[simp] theorem encodeBase_val (x : M31Exact) : (encodeBase x).val = x.val := rfl

theorem encodeBase_cast (x : M31Exact) : ((encodeBase x).val : M31Exact) = x :=
  ZMod.natCast_zmod_val x

theorem eq_encodeBase (x : U32) (y : M31Exact) (hc : x.val < P)
    (h : (x.val : M31Exact) = y) : x = encodeBase y := by
  apply UScalar.eq_of_val_eq
  have hv := congrArg ZMod.val h
  simpa only [ZMod.val_natCast_of_lt hc, encodeBase_val] using hv

theorem mul_encode (x y : M31Exact) :
    field.M31.mul (encodeBase x) (encodeBase y) = .ok (encodeBase (x*y)) := by
  rw [mul_eq]
  obtain ⟨z, hz, hv, hc⟩ := GuardedM31Execution.generated_mul_success (encodeBase x) (encodeBase y)
  rw [hz]
  congr 1
  apply eq_encodeBase z (x*y) hc
  rw [hv, ZMod.natCast_mod, Nat.cast_mul, encodeBase_cast, encodeBase_cast]

theorem add_success (x y : U32) (hx : x.val < P) (hy : y.val < P) :
    ∃ z : U32, field.M31.add x y = .ok z ∧
      z.val = (x.val+y.val)%P ∧ z.val < P := by
  have hsum : x.val+y.val < 2^32 := by unfold P at *; omega
  obtain ⟨s, hs, hv⟩ := InverseRuntimeMul.tryMk_success (ty := .U32) (x.val+y.val) hsum
  change (x + y : Result U32) = .ok s at hs
  have hp : field.P.val = P := by simp [field.P, P]
  by_cases h : P ≤ s.val
  · obtain ⟨z, hz, hzv⟩ := InverseRuntimeMul.sub_success s field.P (by simpa only [hp] using h)
    change (s - field.P : Result U32) = .ok z at hz
    have hc : z.val < P := by rw [hzv, hp, hv]; omega
    refine ⟨z, ?_, ?_, hc⟩
    · simp only [field.M31.add, hs, bind_tc_ok, UScalar.le_equiv, hp, h, if_true, hz]
    · rw [hzv, hp, hv]
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  · have hc : s.val < P := by omega
    refine ⟨s, ?_, ?_, hc⟩
    · simp only [field.M31.add, hs, bind_tc_ok, UScalar.le_equiv, hp, h, if_false]
    · rw [← hv, Nat.mod_eq_of_lt hc]

theorem add_encode (x y : M31Exact) :
    field.M31.add (encodeBase x) (encodeBase y) = .ok (encodeBase (x+y)) := by
  obtain ⟨z, hz, hv, hc⟩ := add_success (encodeBase x) (encodeBase y)
    (ZMod.val_lt x) (ZMod.val_lt y)
  rw [hz]
  congr 1
  apply eq_encodeBase z (x+y) hc
  rw [hv, ZMod.natCast_mod, Nat.cast_add, encodeBase_cast, encodeBase_cast]

theorem neg_encode (x : M31Exact) :
    field.M31.neg (encodeBase x) = .ok (encodeBase (-x)) := by
  have hp : field.P.val = P := by simp [field.P, P]
  have hc : (encodeBase x).val < P := ZMod.val_lt x
  by_cases h : x = 0
  · subst x
    rfl
  · have hx : (encodeBase x).val ≠ 0 := by
      intro hz
      have he := encodeBase_cast x
      rw [hz, Nat.cast_zero] at he
      exact h he.symm
    have hw : encodeBase x ≠ 0#u32 := by
      intro he
      exact hx (congrArg UScalar.val he)
    obtain ⟨z, hz, hv⟩ := InverseRuntimeMul.sub_success field.P (encodeBase x) (by rw [hp]; omega)
    change (field.P - encodeBase x : Result U32) = .ok z at hz
    have hb : z.val < P := by rw [hv, hp]; omega
    simp only [field.M31.neg, hw, if_false, hz, bind_tc_ok]
    congr 1
    apply eq_encodeBase z (-x) hb
    rw [hv, hp, Nat.cast_sub (by omega), encodeBase_cast]
    simp [P, M31Exact]

theorem inv_encode (x : M31Exact) (hx : x ≠ 0) :
    field.M31.inv (encodeBase x) = .ok (encodeBase x⁻¹) := by
  have hn : (encodeBase x).val ≠ 0 := by
    intro hz
    have he := encodeBase_cast x
    rw [hz, Nat.cast_zero] at he
    exact hx he.symm
  rw [inv_eq]
  obtain ⟨z, hz, hc, hv⟩ := GuardedInverseExecution.inverse_correct (encodeBase x) (ZMod.val_lt x) hn
  rw [hz]
  congr 1
  apply eq_encodeBase z x⁻¹ hc
  simpa only [encodeBase_cast] using hv

theorem inv_zero : field.M31.inv (encodeBase 0) = .fail .assertionFailure := by
  rw [inv_eq]
  exact GuardedInverseExecution.zero_rejected

#print axioms reducer_eq
#print axioms mul_eq
#print axioms body_eq
#print axioms loop_eq
#print axioms square_eq
#print axioms inv_eq
#print axioms encodeBase_val
#print axioms encodeBase_cast
#print axioms eq_encodeBase
#print axioms mul_encode
#print axioms add_success
#print axioms add_encode
#print axioms neg_encode
#print axioms inv_encode
#print axioms inv_zero
end AspisV8R19.ComplexBaseExecution

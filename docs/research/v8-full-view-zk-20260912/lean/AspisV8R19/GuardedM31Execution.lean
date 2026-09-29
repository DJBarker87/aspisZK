import AspisV8R19.GuardedFieldSlice
import AspisV8R19.InverseRuntimeMul
import AspisV8R19.CanonicalProduct

/-! Checked-word equivalence for the actual overflow-checked extraction.
The Nat bounds discharge machine operations, casts, guards and fallback. -/
set_option autoImplicit false
namespace AspisV8R19.GuardedM31Execution
open Aeneas Aeneas.Std Result AspisR64Field
open InverseRuntimeMul AspisV8R17.RawReducer
namespace Old
abbrev mul := V7Tag73CurrentHelpersOpaque.aspis_core.field.M31.mul
abbrev reduce := V7Tag73CurrentHelpersOpaque.aspis_core.field.reduce_u64
end Old

theorem reducer_eq (x : U64) : field.reduce_u64 x = Old.reduce x := by
  simp only [field.reduce_u64, Old.reduce,
    V7Tag73CurrentHelpersOpaque.aspis_core.field.reduce_u64,
    field.P, V7Tag73CurrentHelpersOpaque.aspis_core.field.P]

def narrowCond (s : U64) : Result U32 := do
  if P ≤ s.val then
    let d ← UScalar.sub s mask64
    ok (UScalar.cast .U32 d)
  else ok (UScalar.cast .U32 s)

theorem narrowCond_success (s : U64) (hs : s.val < 2*P) :
    ∃ z : U32, narrowCond s = .ok z ∧ z.val = condSubP s.val := by
  by_cases h : P ≤ s.val
  · obtain ⟨d, hd, hv⟩ := sub_success s mask64 (by simpa only [mask64_value] using h)
    have hb : d.val < 2^32 := by rw [hv, mask64_value]; unfold P at *; omega
    refine ⟨UScalar.cast .U32 d, ?_, ?_⟩
    · simp only [narrowCond, h, if_pos, hd, bind_tc_ok]
    · rw [narrow_exact d hb, hv, mask64_value, condSubP, if_pos h]
  · have hb : s.val < 2^32 := by unfold P at *; omega
    refine ⟨UScalar.cast .U32 s, ?_, ?_⟩
    · simp only [narrowCond, if_neg h]
    · rw [narrow_exact s hb, condSubP, if_neg h]

def fastMul (a b : U32) : Result U32 := do
  let product ← UScalar.mul (UScalar.cast .U64 a) (UScalar.cast .U64 b)
  let s ← foldExecution product
  narrowCond s

theorem fastMul_success (a b : U32) (ha : a.val < P) (hb : b.val < P) :
    ∃ z : U32, fastMul a b = .ok z ∧ z.val = (a.val*b.val)%P := by
  have hp := CanonicalProduct.product_lt a.val b.val ha hb
  have hm : (UScalar.cast .U64 a).val * (UScalar.cast .U64 b).val < 2^64 := by
    rw [cast_widen_value, cast_widen_value]
    exact (CanonicalProduct.canonical_execution_bounds a.val b.val ha hb).1
  obtain ⟨product, hm, hv⟩ := mul_success _ _ hm
  rw [cast_widen_value, cast_widen_value] at hv
  obtain ⟨s, hs, hsv⟩ := foldExecution_success product
  obtain ⟨z, hz, hzv⟩ := narrowCond_success s (by
    rw [hsv, hv]; exact CanonicalProduct.fold_lt _ hp)
  refine ⟨z, ?_, ?_⟩
  · simp only [fastMul, hm, hs, hz, bind_tc_ok]
  · rw [hzv, hsv, hv, CanonicalProduct.one_fold_mod _ hp]

theorem generated_branches (a b : U32) :
    field.M31.mul a b =
      if a.val < P ∧ b.val < P then fastMul a b else Old.mul a b := by
  simp only [field.M31.mul, reducer_eq, field.P]
  have hp : (2147483647#u32).val = P := rfl
  by_cases ha : a.val < P <;> by_cases hb : b.val < P
  all_goals
    simp only [UScalar.lt_equiv, hp, ha, hb, and_self,
      and_true, and_false, if_true, if_false]
    simp only [fastMul, narrowCond, foldExecution, Old.mul,
      V7Tag73CurrentHelpersOpaque.aspis_core.field.M31.mul, mask64, mask32,
      lift, bind_tc_ok, bind_assoc_eq] <;> rfl

theorem generated_mul_eq (a b : U32) : field.M31.mul a b = Old.mul a b := by
  rw [generated_branches]
  split
  · rename_i h
    obtain ⟨z, hz, hv⟩ := fastMul_success a b h.1 h.2
    obtain ⟨w, hw, hwv, _⟩ := generated_mul_mod a b
    rw [hz, Old.mul, hw]
    congr 1
    exact UScalar.eq_of_val_eq (hv.trans hwv.symm)
  · rfl

theorem generated_mul_success (a b : U32) :
    ∃ z : U32, field.M31.mul a b = .ok z ∧
      z.val = (a.val*b.val)%P ∧ z.val < P := by
  rw [generated_mul_eq]
  exact generated_mul_mod a b

#print axioms reducer_eq
#print axioms narrowCond_success
#print axioms fastMul_success
#print axioms generated_branches
#print axioms generated_mul_eq
#print axioms generated_mul_success
end AspisV8R19.GuardedM31Execution

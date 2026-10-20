import TerminalV4ReducerOpsV1
import AspisV8R17.RawReducerNat

/-! Reuses the symbolic reducer execution proof over the actual full Aeneas
runtime, then identifies it with freshly extracted current Rust functions.
No source caller canonicality or whole-verifier refinement is assumed. -/
set_option autoImplicit false
namespace AspisR1.TerminalV4Reducer
open Aeneas.Std TerminalV4ReducerOps AspisV8R17.RawReducer

def mask32 : U32 := UScalar.ofNatCore P (by decide)
def mask64 : U64 := UScalar.cast .U64 mask32

theorem mask32_value : mask32.val = P := rfl
theorem mask64_value : mask64.val = P := rfl

def foldExecution (x : U64) : Result U64 := do
  let high ← UScalar.shiftRight x 31
  UScalar.add (UScalar.and x mask64) high

theorem foldExecution_success (x : U64) :
    ∃ y : U64, foldExecution x = .ok y ∧ y.val = foldBits x.val := by
  obtain ⟨high, hs, hv⟩ := shift_success x 31 (by decide)
  have hand : (UScalar.and x mask64).val = x.val &&& P := by
    rw [and_value, mask64_value]
  have hsum : (UScalar.and x mask64).val + high.val < 2^64 := by
    rw [hand, hv]
    have bound := first_fold_lt x.val x.bv.isLt
    change (x.val &&& P) + (x.val >>> 31) < 10737418240 at bound
    omega
  obtain ⟨y, hy, hyv⟩ := add_success _ _ hsum
  refine ⟨y, ?_, ?_⟩
  · simp only [foldExecution, hs, bind_tc_ok, hy]
  · simpa only [hand, hv, foldBits] using hyv

def reduceExecution (x : U64) : Result U32 := do
  let first ← foldExecution x
  let second ← foldExecution first
  let narrowed := UScalar.cast .U32 second
  if P ≤ narrowed.val then UScalar.sub narrowed mask32 else .ok narrowed

theorem reduceExecution_success (x : U64) :
    ∃ y : U32, reduceExecution x = .ok y ∧ y.val = rawReduceU64 x.val := by
  obtain ⟨first, hf, hfv⟩ := foldExecution_success x
  obtain ⟨second, hs, hsv⟩ := foldExecution_success first
  rw [hfv] at hsv
  have narrow : (UScalar.cast .U32 second).val = foldBits (foldBits x.val) := by
    rw [narrow_exact, hsv]
    rw [hsv]
    exact second_fold_lt_two_pow32 x.val x.bv.isLt
  have raw : rawReduceU64 x.val = condSubP (foldBits (foldBits x.val)) := by
    rw [rawReduceU64, second_fold_cast_exact x.val x.bv.isLt]
  by_cases h : P ≤ (UScalar.cast .U32 second).val
  · obtain ⟨y, hy, hyv⟩ := sub_success (UScalar.cast .U32 second) mask32
      (by simpa only [mask32_value] using h)
    refine ⟨y, ?_, ?_⟩
    · simp only [reduceExecution, hf, hs, bind_tc_ok, h, if_pos, hy]
    · rw [raw, condSubP, ← narrow, if_pos h]
      simpa only [mask32_value] using hyv
  · refine ⟨UScalar.cast .U32 second, ?_, ?_⟩
    · simp only [reduceExecution, hf, hs, bind_tc_ok, h, if_false]
    · rw [raw, condSubP, ← narrow, if_neg h]

theorem reduceExecution_canonical (x : U64) :
    ∃ y : U32, reduceExecution x = .ok y ∧ y.val = rawReduceU64 x.val ∧ y.val < P := by
  obtain ⟨y, hy, hv⟩ := reduceExecution_success x
  refine ⟨y, hy, hv, ?_⟩
  rw [hv]
  exact rawReduceU64_canonical x.val x.bv.isLt

#print axioms foldExecution_success
theorem reduceExecution_mod (x : U64) :
    ∃ y : U32, reduceExecution x = .ok y ∧ y.val = x.val % P ∧ y.val < P := by
  obtain ⟨y, hy, hv, hc⟩ := reduceExecution_canonical x
  exact ⟨y, hy, hv.trans (rawReduceU64_eq_mod_nat x.val x.bv.isLt), hc⟩

#print axioms reduceExecution_success
#print axioms reduceExecution_canonical
#print axioms reduceExecution_mod


/-- Actual extracted current reducer equals the symbolic execution above. -/
theorem current_reducer_eq (x : U64) :
    AspisR1SelectedMaskProbe.field.reduce_u64 x = reduceExecution x := by
  simp only [AspisR1SelectedMaskProbe.field.reduce_u64,
    AspisR1SelectedMaskProbe.field.P, reduceExecution,
    foldExecution, mask64, mask32, lift, bind_tc_ok, bind_assoc_eq]
  rfl

theorem current_reduce_mod (x : U64) :
    ∃ z : U32, AspisR1SelectedMaskProbe.field.reduce_u64 x = .ok z ∧
      z.val = x.val % P ∧ z.val < P := by
  rw [current_reducer_eq]
  exact reduceExecution_mod x

theorem cast_widen_value (x : U32) : (UScalar.cast .U64 x).val = x.val := by
  rw [cast_value]
  apply Nat.mod_eq_of_lt
  have h := x.bv.isLt
  change x.val < 2^32 at h
  change x.val < 2^64
  omega

/-- Every pair of stored U32 inputs fits the widening product; no canonical
input premise is needed for multiplication itself. -/
theorem current_mul_mod (x y : AspisR1SelectedMaskProbe.field.M31) :
    ∃ z : AspisR1SelectedMaskProbe.field.M31,
      AspisR1SelectedMaskProbe.field.M31.mul x y = .ok z ∧
      z.val = (x.val*y.val) % P ∧ z.val < P := by
  have hproduct : (UScalar.cast .U64 x).val * (UScalar.cast .U64 y).val < 2^64 := by
    rw [cast_widen_value, cast_widen_value]
    have h := Nat.mul_lt_mul_of_lt_of_lt x.bv.isLt y.bv.isLt
    exact h
  obtain ⟨product, hp, hv⟩ := mul_success _ _ hproduct
  rw [cast_widen_value, cast_widen_value] at hv
  obtain ⟨z, hz, hzm, hzc⟩ := current_reduce_mod product
  refine ⟨z, ?_, ?_, hzc⟩
  · simp only [AspisR1SelectedMaskProbe.field.M31.mul, lift, bind_tc_ok]
    change (do
      let p ← UScalar.mul (UScalar.cast .U64 x) (UScalar.cast .U64 y)
      let r ← AspisR1SelectedMaskProbe.field.reduce_u64 p
      Result.ok r) = Result.ok z
    simp only [hp, bind_tc_ok, hz]
  · simpa only [hv] using hzm

theorem current_wrapper_mod (x : U64) :
    ∃ z : AspisR1SelectedMaskProbe.field.M31,
      AspisR1SelectedMaskProbe.field.M31.reduce_u64 x = .ok z ∧
      z.val = x.val % P ∧ z.val < P := by
  obtain ⟨z, hz, hm, hc⟩ := current_reduce_mod x
  exact ⟨z, by simp only [AspisR1SelectedMaskProbe.field.M31.reduce_u64,
    hz, bind_tc_ok], hm, hc⟩

#print axioms current_reducer_eq
#print axioms current_reduce_mod
#print axioms cast_widen_value
#print axioms current_mul_mod
#print axioms current_wrapper_mod
end AspisR1.TerminalV4Reducer

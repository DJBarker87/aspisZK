import AspisV8R17.UnsignedReducerOps
import AspisV8R17.RawReducerNat

/-! Composition of authenticated runtime operations using the retained reducer
bounds. Literal generated constant/notation/comparison binding is still separate.
No theorem here asserts equality to the full extracted reduce_u64 declaration. -/
namespace AspisV8R17.UnsignedReducerExecution
open Aeneas.Std UnsignedReducerOps UnsignedCoreSlice RawReducer

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
end AspisV8R17.UnsignedReducerExecution

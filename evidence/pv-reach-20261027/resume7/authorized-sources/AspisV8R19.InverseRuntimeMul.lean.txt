import AspisV8R19.InverseFieldSlice
import AspisV8R17.RawReducerNat

/-! R17 reducer arguments replayed against the full Aeneas scalar runtime.
No projected scalar definitions are imported. -/
namespace AspisV8R19.InverseRuntimeMul
open Aeneas.Std V7Tag73CurrentHelpersOpaque AspisV8R17.RawReducer
open AspisV8R17

theorem tryMk_success {ty : UScalarTy} (n : Nat) (h : n < 2^ty.numBits) :
    ∃ z : UScalar ty, UScalar.tryMk ty n = .ok z ∧ z.val = n := by
  refine ⟨UScalar.ofNatCore n h, ?_, rfl⟩
  simp [UScalar.tryMk, UScalar.tryMkOpt, UScalar.check_bounds, h, Result.ofOption]

theorem add_success (x y : UScalar .U64) (h : x.val + y.val < 2^64) :
    ∃ z : UScalar .U64, UScalar.add x y = .ok z ∧ z.val = x.val + y.val :=
  tryMk_success _ h

theorem mul_success (x y : UScalar .U64) (h : x.val * y.val < 2^64) :
    ∃ z : UScalar .U64, UScalar.mul x y = .ok z ∧ z.val = x.val * y.val :=
  tryMk_success _ h

theorem tryMk_overflow {ty : UScalarTy} (n : Nat) (h : ¬n < 2^ty.numBits) :
    UScalar.tryMk ty n = .fail .integerOverflow := by
  simp [UScalar.tryMk, UScalar.tryMkOpt, UScalar.check_bounds, h, Result.ofOption]

theorem cast_value {ty : UScalarTy} (x : UScalar ty) (target : UScalarTy) :
    (UScalar.cast target x).val = x.val % 2^target.numBits := by
  exact BitVec.toNat_setWidth _ _

theorem narrow_exact (x : U64) (h : x.val < 2^32) :
    (UScalar.cast .U32 x).val = x.val := by
  rw [cast_value]
  exact Nat.mod_eq_of_lt h

theorem and_value {ty : UScalarTy} (x y : UScalar ty) :
    (UScalar.and x y).val = x.val &&& y.val :=
  BitVec.toNat_and _ _

theorem shift_success {ty : UScalarTy} (x : UScalar ty) (s : Nat) (h : s < ty.numBits) :
    ∃ z : UScalar ty, UScalar.shiftRight x s = .ok z ∧ z.val = x.val >>> s := by
  refine ⟨⟨x.bv.ushiftRight s⟩, ?_, BitVec.toNat_ushiftRight _ _⟩
  simp only [UScalar.shiftRight, h, if_pos]

theorem sub_success {ty : UScalarTy} (x y : UScalar ty) (h : y.val ≤ x.val) :
    ∃ z : UScalar ty, UScalar.sub x y = .ok z ∧ z.val = x.val-y.val := by
  refine ⟨⟨BitVec.ofNat _ (x.val-y.val)⟩, ?_, ?_⟩
  · simp only [UScalar.sub, Nat.not_lt.mpr h, if_false]
  · change (x.val-y.val) % 2^ty.numBits = x.val-y.val
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) x.bv.isLt

theorem shift_overflow {ty : UScalarTy} (x : UScalar ty) (s : Nat) (h : ¬s < ty.numBits) :
    UScalar.shiftRight x s = .fail .integerOverflow := by
  simp only [UScalar.shiftRight, h, if_false]

theorem sub_underflow {ty : UScalarTy} (x y : UScalar ty) (h : x.val < y.val) :
    UScalar.sub x y = .fail .integerOverflow := by
  simp only [UScalar.sub, h, if_pos]

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

theorem reduceExecution_mod (x : U64) :
    ∃ y : U32, reduceExecution x = .ok y ∧ y.val = x.val % P ∧ y.val < P := by
  obtain ⟨y, hy, hv, hc⟩ := reduceExecution_canonical x
  exact ⟨y, hy, hv.trans (rawReduceU64_eq_mod_nat x.val x.bv.isLt), hc⟩

theorem generated_reducer_eq (x : U64) :
    aspis_core.field.reduce_u64 x = reduceExecution x := by
  simp only [aspis_core.field.reduce_u64, aspis_core.field.P, reduceExecution,
    foldExecution, mask64, mask32, lift, bind_tc_ok, bind_assoc_eq]
  rfl

theorem generated_reducer_mod (x : U64) :
    ∃ y : U32, aspis_core.field.reduce_u64 x = .ok y ∧
      y.val = x.val % RawReducer.P ∧ y.val < RawReducer.P := by
  rw [generated_reducer_eq]
  exact reduceExecution_mod x


theorem cast_widen_value (x : U32) : (UScalar.cast .U64 x).val = x.val := by
  rw [cast_value]
  apply Nat.mod_eq_of_lt
  have h := x.bv.isLt
  change x.val < 2^32 at h
  change x.val < 2^64
  omega

theorem generated_mul_mod (x y : aspis_core.field.M31) :
    ∃ z : aspis_core.field.M31, aspis_core.field.M31.mul x y = .ok z ∧
      z.val = (x.val*y.val) % RawReducer.P ∧ z.val < RawReducer.P := by
  have hproduct : (UScalar.cast .U64 x).val * (UScalar.cast .U64 y).val < 2^64 := by
    rw [cast_widen_value, cast_widen_value]
    have h := Nat.mul_lt_mul_of_lt_of_lt x.bv.isLt y.bv.isLt
    exact h
  obtain ⟨product, hp, hv⟩ := mul_success _ _ hproduct
  rw [cast_widen_value, cast_widen_value] at hv
  obtain ⟨z, hz, hzm, hzc⟩ := generated_reducer_mod product
  refine ⟨z, ?_, ?_, hzc⟩
  · simp only [aspis_core.field.M31.mul, lift, bind_tc_ok]
    change (do
      let p ← UScalar.mul (UScalar.cast .U64 x) (UScalar.cast .U64 y)
      let r ← aspis_core.field.reduce_u64 p
      Result.ok r) = Result.ok z
    simp only [hp, bind_tc_ok, hz]
  · simpa only [hv] using hzm

#print axioms tryMk_success
#print axioms add_success
#print axioms mul_success
#print axioms tryMk_overflow
#print axioms cast_value
#print axioms narrow_exact
#print axioms and_value
#print axioms shift_success
#print axioms sub_success
#print axioms shift_overflow
#print axioms sub_underflow
#print axioms mask32_value
#print axioms mask64_value
#print axioms foldExecution_success
#print axioms reduceExecution_success
#print axioms reduceExecution_canonical
#print axioms reduceExecution_mod
#print axioms generated_reducer_eq
#print axioms generated_reducer_mod
#print axioms cast_widen_value
#print axioms generated_mul_mod
end AspisV8R19.InverseRuntimeMul

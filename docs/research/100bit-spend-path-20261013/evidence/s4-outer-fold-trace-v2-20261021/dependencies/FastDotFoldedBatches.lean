import AspisR1BatchedReducerBridge
import Mathlib.Data.List.Basic

set_option autoImplicit false
namespace AspisR1.FastDotFoldedBatches
open AspisR1BatchedFoldArithmetic
open Aeneas.Std

def cap : Nat := (2^31-2)^2

def foldedSum : List (List Nat) → Nat
  | [] => 0
  | xs :: rest => fold xs.sum + foldedSum rest

def fullSum : List (List Nat) → Nat
  | [] => 0
  | xs :: rest => xs.sum + fullSum rest

theorem batch_sum_le (xs : List Nat) (hxs : ∀ x ∈ xs, x ≤ cap) :
    xs.sum ≤ xs.length * cap := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hxs x (by simp)
    have ht := ih (fun y hy => hxs y (by simp [hy]))
    simp only [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem batch_sum_u64 (xs : List Nat) (hlen : xs.length ≤ 4)
    (hxs : ∀ x ∈ xs, x ≤ cap) : xs.sum < 2^64 := by
  have hsum := batch_sum_le xs hxs
  have hmul := Nat.mul_le_mul_right cap hlen
  have hc : 4*cap < 2^64 := by norm_num [cap]
  omega

theorem foldedSum_bound (batches : List (List Nat))
    (hb : ∀ xs ∈ batches, xs.length ≤ 4 ∧ ∀ x ∈ xs, x ≤ cap) :
    foldedSum batches ≤ batches.length * (2^34-1) := by
  induction batches with
  | nil => simp [foldedSum]
  | cons xs rest ih =>
    have hx := hb xs (by simp)
    have hf := fold_lt_two34 (batch_sum_u64 xs hx.1 hx.2)
    have ht := ih (fun ys hy => hb ys (by simp [hy]))
    simp only [foldedSum, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem seven_batches_u64 (batches : List (List Nat))
    (hlen : batches.length ≤ 7)
    (hb : ∀ xs ∈ batches, xs.length ≤ 4 ∧ ∀ x ∈ xs, x ≤ cap) :
    foldedSum batches < 2^37 ∧ foldedSum batches < 2^64 := by
  have hs := foldedSum_bound batches hb
  have hm := Nat.mul_le_mul_right (2^34-1) hlen
  norm_num at hm
  omega

theorem foldedSum_mod (batches : List (List Nat)) :
    foldedSum batches % modulus = fullSum batches % modulus := by
  induction batches with
  | nil => rfl
  | cons xs rest ih =>
    change (fold xs.sum + foldedSum rest) % modulus =
      (xs.sum + fullSum rest) % modulus
    calc
      (fold xs.sum + foldedSum rest) % modulus =
        ((fold xs.sum)%modulus + (foldedSum rest)%modulus)%modulus := Nat.add_mod _ _ _
      _ = (xs.sum%modulus + (fullSum rest)%modulus)%modulus := by rw [fold_preserves_mod, ih]
      _ = (xs.sum + fullSum rest)%modulus := (Nat.add_mod _ _ _).symm

/-- Source-shaped base-dot batches: seven groups, at most four canonical-limb
products per group. Applying the retained actual reducer yields exactly the
unreduced sum. Array/byte decoding and Rust-loop linkage are separate. -/
theorem actual_reducer_after_seven (batches : List (List Nat))
    (hlen : batches.length ≤ 7)
    (hb : ∀ xs ∈ batches, xs.length ≤ 4 ∧ ∀ x ∈ xs, x ≤ cap) :
    ∃ z : AspisR1Qm31ArithmeticProbe.field.M31,
      AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64
        (UScalar.ofNatCore (foldedSum batches) (seven_batches_u64 batches hlen hb).2)
        = .ok z ∧
      z.val = fullSum batches % modulus ∧ z.val < modulus := by
  obtain ⟨z, hz, hmod, hcanonical⟩ :=
    AspisR1.ExtractedCurrentReducer.current_wrapper_mod
      (show U64 from UScalar.ofNatCore (foldedSum batches) (seven_batches_u64 batches hlen hb).2)
  have hval : (UScalar.ofNatCore (foldedSum batches)
      (seven_batches_u64 batches hlen hb).2 : U64).val = foldedSum batches := rfl
  rw [hval] at hmod
  refine ⟨z, hz, ?_, ?_⟩
  · simpa [modulus] using hmod.trans (foldedSum_mod batches)
  · simpa [modulus] using hcanonical

#print axioms batch_sum_u64
#print axioms seven_batches_u64
#print axioms foldedSum_mod
#print axioms actual_reducer_after_seven
end AspisR1.FastDotFoldedBatches

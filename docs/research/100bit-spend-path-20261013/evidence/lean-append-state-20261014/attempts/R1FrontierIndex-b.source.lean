import AspisFormal.Pool.IncrementalMerkleV1
import Mathlib.Data.Nat.Bitwise

/-! The binary live-slot pattern of a frontier records the low bits of its
Nat index, with slot zero as the least significant bit. -/
set_option autoImplicit false

namespace AspisR1.FrontierIndex

open AspisPool.IncrementalMerkleV1

def indexedSlots {α : Type} (n index : Nat) (values : Fin n → α) : List (Option α) :=
  List.ofFn fun i : Fin n =>
    if ((index >>> i.val) &&& 1) = 0 then none else some (values i)

theorem indexedSlots_frontierValue {α : Type} (n index : Nat) (values : Fin n → α) :
    frontierValue (indexedSlots n index values) = index % 2 ^ n := by
  induction n generalizing index with
  | zero => simp [indexedSlots, frontierValue, Nat.mod_one]
  | succ n ih =>
      rw [indexedSlots, List.ofFn_succ]
      have hshift (i : Fin n) :
          index >>> i.succ.val = (index >>> 1) >>> i.val := by
        rw [show i.succ.val = i.val + 1 by rfl, Nat.add_comm i.val 1]
        exact Nat.shiftRight_add index 1 i.val
      have htail :
          List.ofFn (fun i : Fin n =>
            if ((index >>> i.succ.val) &&& 1) = 0 then none else some (values i.succ)) =
          indexedSlots n (index >>> 1) (fun i => values i.succ) := by
        unfold indexedSlots
        congr 1
        funext i
        rw [hshift i]
      rw [htail]
      simp only [frontierValue, Nat.shiftRight_zero]
      change (if (index &&& 1) = 0 then
        2 * frontierValue (indexedSlots n (index >>> 1) fun i => values i.succ)
        else 1 + 2 * frontierValue (indexedSlots n (index >>> 1) fun i => values i.succ)) =
        index % 2 ^ (n + 1)
      have hlow : index &&& 1 = index % 2 := by
        calc
          index &&& 1 = (index.testBit 0).toNat := by simpa using Nat.and_two_pow index 0
          _ = index / 2 ^ 0 % 2 := Nat.toNat_testBit index 0
          _ = index % 2 := by simp
      have hrem : index % 2 ^ (n + 1) = index % 2 + 2 * (index / 2 % 2 ^ n) := by
        rw [show 2 ^ (n + 1) = 2 * 2 ^ n by rw [pow_succ]]
        exact Nat.mod_mul
      have htailValue :
          frontierValue (indexedSlots n (index >>> 1) fun i => values i.succ) =
            index / 2 % 2 ^ n := by
        rw [ih]
        rw [Nat.shiftRight_eq_div_pow]
        simp
      rw [hlow, hrem, htailValue]
      rcases Nat.mod_two_eq_zero_or_one index with hzero | hone
      · rw [if_pos hzero]
        omega
      · have hne : index % 2 ≠ 0 := by omega
        rw [if_neg (by omega)]
        omega

theorem indexedSlots_frontierValue_of_lt {α : Type} (n index : Nat)
    (values : Fin n → α) (hindex : index < 2 ^ n) :
    frontierValue (indexedSlots n index values) = index := by
  rw [indexedSlots_frontierValue]
  exact Nat.mod_eq_of_lt hindex

#print axioms indexedSlots_frontierValue
#print axioms indexedSlots_frontierValue_of_lt

end AspisR1.FrontierIndex

import PV_L2C_QBalance
import PV_L2C_PaddingProducer
import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit false
namespace PV_L2C_QFold
open PV_L2C_NativeQ PV_L2C_QBalance

theorem canonical_fold (xs : List Q) (hxs : ∀ q ∈ xs, Canonical q)
    (s : Q) (hs : Canonical s) : Canonical (foldQ xs s) := by
  induction xs generalizing s with
  | nil => exact hs
  | cons q qs ih =>
    exact ih (fun q hq => hxs q (by simp [hq])) (addQ s q)
      (add_canonical s q hs (hxs q (by simp)))
#print axioms canonical_fold

theorem decode_fold (xs : List Q) (hxs : ∀ q ∈ xs, Canonical q)
    (s : Q) (hs : Canonical s) :
    decodeQ (foldQ xs s)=decodeQ s+(xs.map decodeQ).sum := by
  induction xs generalizing s with
  | nil => simp [foldQ]
  | cons q qs ih =>
    rw [foldQ,ih (fun q hq => hxs q (by simp [hq])) (addQ s q)
      (add_canonical s q hs (hxs q (by simp))),add_decode s q hs (hxs q (by simp))]
    simp [add_assoc]
#print axioms decode_fold

/-- The ascending row fold of a full fixed-length native table. -/
def tableSum {n : Nat} (table : Fin n → Q) : Q := foldQ (List.ofFn table) zero

theorem tableSum_canonical {n : Nat} (table : Fin n → Q)
    (hc : ∀ i, Canonical (table i)) : Canonical (tableSum table) := by
  apply canonical_fold _ _ zero zero_canonical
  intro q hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  exact hc i
#print axioms tableSum_canonical

theorem tableSum_decode {n : Nat} (table : Fin n → Q)
    (hc : ∀ i, Canonical (table i)) :
    decodeQ (tableSum table)=∑ i : Fin n, decodeQ (table i) := by
  unfold tableSum
  rw [decode_fold _ (by intro q hq; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq; exact hc i) zero zero_canonical]
  simp [zero_decode,List.map_ofFn,List.sum_ofFn]
#print axioms tableSum_decode

/-- Active rows are public. Their source step skips addition. This table
projection inserts zero at exactly those rows; native canonical add-zero is
proved below rather than assumed to be raw modular normalization. -/
def inactiveTable {n : Nat} (active : Fin n → Bool) (table : Fin n → Q) : Fin n → Q :=
  fun i => if active i then zero else table i

theorem inactive_canonical {n : Nat} (active : Fin n → Bool) (table : Fin n → Q)
    (hc : ∀ i, Canonical (table i)) : ∀ i, Canonical (inactiveTable active table i) := by
  intro i
  cases hi : active i <;> simp [inactiveTable,hi,zero_canonical,hc i]
#print axioms inactive_canonical

theorem inactive_decode {n : Nat} (active : Fin n → Bool) (table : Fin n → Q)
    (hc : ∀ i, Canonical (table i)) :
    decodeQ (tableSum (inactiveTable active table))=
      PV_L2C_PaddingProducer.inactiveSum active (fun i => decodeQ (table i)) := by
  rw [tableSum_decode _ (inactive_canonical active table hc)]
  unfold PV_L2C_PaddingProducer.inactiveSum
  apply Finset.sum_congr rfl
  intro i hi
  cases ha : active i <;> simp [inactiveTable,ha,zero_decode]
#print axioms inactive_decode

theorem native_add_zero (s : Q) (hs : Canonical s) : addQ s zero=s := by
  apply decode_injective _ _ (add_canonical s zero hs zero_canonical) hs
  rw [add_decode s zero hs zero_canonical,zero_decode,add_zero]
#print axioms native_add_zero
end PV_L2C_QFold

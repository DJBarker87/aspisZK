import CheckpointBytes4RawFields

set_option autoImplicit false
namespace AspisR1.CheckpointBytes4QueryWord
open Aeneas Aeneas.Std

/-- Symbolic little-endian content, proved by byte recursion and disjoint
low/high bit ranges rather than a native bitvector decision procedure. -/
theorem from_le_nat (bs : List (BitVec 8)) :
    (BitVec.fromLEBytes bs).toNat = bs.foldr (fun b n => b.toNat+256*n) 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change (b.setWidth (8*(bs.length+1)) |||
      ((BitVec.fromLEBytes bs).setWidth (8*(bs.length+1)) <<< 8)).toNat =
        b.toNat + 256*(bs.foldr (fun b n => b.toNat+256*n) 0)
    rw [BitVec.toNat_or,BitVec.toNat_shiftLeft,
      BitVec.toNat_setWidth_of_le (by omega),BitVec.toNat_setWidth_of_le (by omega)]
    have shiftBound : (BitVec.fromLEBytes bs).toNat <<< 8 < 2^(8*(bs.length+1)) := by
      have h := (BitVec.fromLEBytes bs).isLt
      rw [Nat.shiftLeft_eq,show 8*(bs.length+1) = 8*bs.length+8 by omega,Nat.pow_add]
      change (BitVec.fromLEBytes bs).toNat * 256 < 2^(8*bs.length)*256
      omega
    rw [Nat.mod_eq_of_lt shiftBound,Nat.or_comm,
      ← Nat.shiftLeft_add_eq_or_of_lt b.isLt,Nat.shiftLeft_eq,ih]
    omega

#print axioms from_le_nat
end AspisR1.CheckpointBytes4QueryWord

import Aeneas
set_option autoImplicit false
namespace PV_B2_D_ReducerBounds
-- Symbolic fold bounds: no SAT/native evaluation and no field-chain reduction.
def fold64 (x : BitVec 64) : BitVec 64 := (x &&& 2147483647#64) + (x >>> 31)
def word (x : BitVec 64) : BitVec 32 := (fold64 (fold64 x)).setWidth 32
def reduced (x : BitVec 64) : BitVec 32 :=
  word x - (2147483647#32 &&& (0#32 - (if (2147483647#32).ule (word x) then 1#32 else 0#32)))

theorem fold_val (x : BitVec 64) : (fold64 x).toNat =
    (x.toNat % 2147483648 + x.toNat / 2147483648) % 18446744073709551616 := by
  simp only [fold64,BitVec.toNat_add,BitVec.toNat_and,BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  change ((x.toNat &&& (2^31-1)) + x.toNat / 2147483648) % 18446744073709551616 = _
  rw [Nat.and_two_pow_sub_one_eq_mod]

theorem fold_le (x : BitVec 64) : (fold64 x).toNat ≤
    x.toNat % 2147483648 + x.toNat / 2147483648 := by
  rw [fold_val]
  exact Nat.mod_le _ _

theorem word_bound (x : BitVec 64) : (word x).toNat < 4294967294 := by
  have hx := x.isLt
  change x.toNat < 18446744073709551616 at hx
  have h1 := fold_le x
  have hy : (fold64 x).toNat ≤ 10737418238 := by omega
  have h2 := fold_le (fold64 x)
  have hz : (fold64 (fold64 x)).toNat < 4294967294 := by omega
  rw [word,BitVec.toNat_setWidth]
  exact lt_of_le_of_lt (Nat.mod_le _ _) hz

theorem bitvec_bound (x : BitVec 64) : (reduced x).toNat < 2147483647 := by
  have hw := word_bound x
  by_cases h : 2147483647 ≤ (word x).toNat
  · simp only [reduced,BitVec.ule,show (2147483647#32).toNat = 2147483647 from rfl,
      h,decide_true,if_pos]
    change (word x - 2147483647#32).toNat < 2147483647
    rw [BitVec.toNat_sub_of_le (show 2147483647#32 ≤ word x from h)]
    change (word x).toNat - 2147483647 < 2147483647
    omega
  · simp only [reduced,BitVec.ule,show (2147483647#32).toNat = 2147483647 from rfl,
      h,decide_false,if_neg]
    change (word x - 0#32).toNat < 2147483647
    simpa only [BitVec.sub_zero] using Nat.lt_of_not_ge h

#print axioms fold_val
#print axioms fold_le
#print axioms word_bound
#print axioms bitvec_bound
end PV_B2_D_ReducerBounds

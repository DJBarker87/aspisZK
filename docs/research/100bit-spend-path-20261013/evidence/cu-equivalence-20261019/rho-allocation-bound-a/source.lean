import Aeneas

/-! Arithmetic part of the pinned Solana BumpAllocator contract for [u64;4].
This proves the exact alignment mask cannot consume more than seven bytes.
It is not a proof of Vec reservation, pointer ownership or the whole caller's
heap budget; those source/resource bindings remain explicit.
-/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoAllocationBound
open Aeneas Aeneas.Std Result

theorem clear_low_three_bounds (x : BitVec 64) :
    (x &&& ~~~(7 : BitVec 64)).toNat ≤ x.toNat ∧
      x.toNat ≤ (x &&& ~~~(7 : BitVec 64)).toNat+7 := by
  let y := x &&& ~~~(7 : BitVec 64)
  have hle : y ≤ x := by dsimp only [y];bv_decide
  have hmax : y ≤ (18446744073709551608 : BitVec 64) := by dsimp only [y];bv_decide
  have hround : x ≤ y+(7 : BitVec 64) := by dsimp only [y];bv_decide
  change y.toNat ≤ x.toNat at hle
  change y.toNat ≤ 18446744073709551608 at hmax
  change x.toNat ≤ (y+(7 : BitVec 64)).toNat at hround
  rw [BitVec.toNat_add] at hround
  change x.toNat ≤ (y.toNat+7)%18446744073709551616 at hround
  rw [Nat.mod_eq_of_lt (by omega)] at hround
  exact ⟨hle,hround⟩

def align8 (value : U64) : U64 := UScalar.and value (UScalar.not 7#u64)

theorem align8_bounds (value : U64) :
    (align8 value).val ≤ value.val ∧ value.val ≤ (align8 value).val+7 := by
  exact clear_low_three_bounds value.bv

def allocatePosition (base cursor size : Nat) (hcursor : cursor < 2^64) : Option Nat :=
  let subtracted : U64 := UScalar.ofNatCore (cursor-size)
    (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hcursor)
  let aligned := (align8 subtracted).val
  if aligned < base+8 then none else some aligned

theorem allocation_success (base cursor count : Nat) (hc : cursor < 2^64)
    (hfree : base+8+32*count+7 ≤ cursor) :
    ∃ position,
      allocatePosition base cursor (32*count) hc = some position ∧
      base+8 ≤ position ∧ position+32*count ≤ cursor ∧
      cursor ≤ position+32*count+7 := by
  let subtracted : U64 := UScalar.ofNatCore (cursor-32*count)
    (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hc)
  have hb := align8_bounds subtracted
  change (align8 subtracted).val ≤ cursor-32*count ∧
    cursor-32*count ≤ (align8 subtracted).val+7 at hb
  have hsize : 32*count ≤ cursor := by omega
  have hsub : cursor-32*count+32*count = cursor := Nat.sub_add_cancel hsize
  have hbase : base+8 ≤ (align8 subtracted).val := by omega
  refine ⟨(align8 subtracted).val,?_,hbase,by omega,by omega⟩
  change (if (align8 subtracted).val < base+8 then none else some _) = _
  rw [if_neg (Nat.not_lt.mpr hbase)]

theorem raw_layout_budget (count : Nat) (hn : count ≤ 256) :
    32*count+7 ≤ 8199 := by omega

theorem s2_layout_budget : 32*64+7 = 2055 := by decide

#print axioms clear_low_three_bounds
#print axioms align8_bounds
#print axioms allocation_success
#print axioms raw_layout_budget
#print axioms s2_layout_budget
end AspisR1.CuSavingsRhoAllocationBound

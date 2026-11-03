import R1Z.PV_V263_RawGrowth
/-! Layout::repeat's alignment-sensitive isize bound. For type layouts whose
size is an alignment multiple and whose alignment divides isize::MAX+1,
the byte limit used in RawGrowth is equivalent to the actual Layout bound.
This is arithmetic; native type-layout and bit-rounding association remain. -/
set_option autoImplicit false
namespace R1Z.PV_V263_LayoutBounds
open Aeneas.Std

theorem aligned_limit (limit align k q : Nat) (positive : 0<align)
    (top : limit+1=q*align) :
    k*align≤limit ↔ k*align≤limit+1-align := by
  constructor
  · intro small
    have less : k<q := by
      by_contra h
      have ge : q≤k := by omega
      have multiplied := Nat.mul_le_mul_right align ge
      omega
    have multiplied := Nat.mul_le_mul_right align (show k+1≤q by omega)
    rw [Nat.add_mul,Nat.one_mul] at multiplied
    omega
  · intro bounded
    have h : limit+1-align≤limit := by omega
    exact bounded.trans h

theorem array_limit (size align count k q limit : Nat)
    (positive : 0<align) (typeSize : size=k*align)
    (top : limit+1=q*align) :
    count*size≤limit ↔ count*size≤limit+1-align := by
  rw [typeSize,←Nat.mul_assoc]
  exact aligned_limit limit align (count*k) q positive top

/-- A valid sized RawVec allocation guarantees the unchecked doubling used
by grow_amortized cannot overflow the usize arithmetic. -/
theorem doubling (raw size : Nat) (positive : 0<size)
    (valid : raw*size≤Usize.max/2) : raw*2≤Usize.max := by
  have raw_le : raw≤raw*size := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left raw positive
  have bounded := Nat.mul_le_mul_right 2 (raw_le.trans valid)
  exact bounded.trans (Nat.div_mul_le_self _ _)

#print axioms aligned_limit
#print axioms array_limit
#print axioms doubling
end R1Z.PV_V263_LayoutBounds

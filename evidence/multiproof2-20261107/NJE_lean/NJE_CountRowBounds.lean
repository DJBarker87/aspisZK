import NJE_CountArithmetic
import MultiproofConeCountPhysical

set_option autoImplicit false
namespace NJE_CountRowBounds
open Aeneas Aeneas.Std
open AspisR1.MultiproofConeLiveOrder

def cost (k : Nat → Nat) (n i : Nat) : Nat := if pairAt k n i then 0 else 1

theorem deficit (k : Nat → Nat) (n i : Nat) :
    2-(advance k n i-i)=cost k n i := by
 unfold advance cost
 split <;> omega

theorem cost_bound (k : Nat → Nat) (n i : Nat) : cost k n i≤1 := by
 unfold cost
 split <;> omega

theorem progress (k : Nat → Nat) (n i : Nat) : cost k n i≤advance k n i-i := by
 unfold cost advance
 split <;> omega

theorem count_value (k : Nat → Nat) (n : Nat) (c i q : Usize)
    (cb : c.val≤576) (q_value : q.val=advance k n i.val) :
    (Usize.wrapping_add c (Usize.wrapping_sub 2#usize (Usize.wrapping_sub q i))).val=
      c.val+cost k n i.val := by
 have lower : i.val≤q.val := by rw [q_value];unfold advance;split <;> omega
 have upper : q.val ≤ i.val+2 := by rw [q_value];unfold advance;split <;> omega
 rw [NJE_CountArithmetic.count_value c i q cb lower upper,q_value,deficit]

#print deficit
#print axioms deficit
#print cost_bound
#print axioms cost_bound
#print progress
#print axioms progress
#print count_value
#print axioms count_value
end NJE_CountRowBounds

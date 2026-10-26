import PoolL_LengthFacts
set_option autoImplicit false
namespace AspisR1.PoolL_LengthOccupied
open Aeneas Aeneas.Std Result PoolL_LengthSource

/-- All non-checkpoint data widths in the live write-role inventory. -/
def OtherWidth (n : Nat) : Prop :=
  n = 384 ∨ n = 768 ∨ n = 1000 ∨ n = 8256 ∨ n = 10000 ∨ n = 8504 ∨
  n = 208 ∨ n = 165 ∨ n = 82

theorem disjoint (n size : Nat) (cp : n = 192 ∨ n = 1768) (other : OtherWidth size) :
    n ≠ size := by
  rcases cp with cp | cp <;>
    rcases other with h | h | h | h | h | h | h | h | h <;> omega

/-- First length disjunct rejects every occupied checkpoint in another role.
This theorem does not substitute InvalidAccountType for distinct token errors. -/
theorem rejects (data : Slice U8) (size : Usize)
    (cp : data.val.length = 192 ∨ data.val.length = 1768) (other : OtherWidth size.val) :
    lengthPrefix data size = ok (.Err (.Custom 1095966721#u32)) :=
  PoolL_LengthFacts.wrong data size (disjoint _ _ cp other)

#print axioms disjoint
#print axioms rejects
end AspisR1.PoolL_LengthOccupied

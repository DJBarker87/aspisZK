import Aeneas
namespace R1Z.PV_CBL_SplitBounds
set_option autoImplicit false

/-- A complete block never reads outside the supplied slice. -/
theorem block_index (len size i j : Nat) (hi : i < len/size) (hj : j<size) :
    i*size+j<len := by
  have hcount : (i+1)*size ≤ (len/size)*size :=
    Nat.mul_le_mul_right size (by omega)
  have hlast : i*size+j < (i+1)*size := by
    simpa only [Nat.add_mul,Nat.one_mul] using Nat.add_lt_add_left hj (i*size)
  exact lt_of_lt_of_le hlast (le_trans hcount (Nat.div_mul_le_self len size))

theorem prefix_bound (len size : Nat) : (len/size)*size≤len :=
  Nat.div_mul_le_self len size

theorem consumed_and_tail (len size : Nat) : (len/size)*size+len%size=len := by
  simpa only [Nat.mul_comm] using Nat.div_add_mod len size

theorem tail_index (len size k : Nat) (hk : k<len%size) :
    (len/size)*size+k<len := by
  have := consumed_and_tail len size
  omega

#print axioms block_index
#print axioms prefix_bound
#print axioms consumed_and_tail
#print axioms tail_index
end R1Z.PV_CBL_SplitBounds

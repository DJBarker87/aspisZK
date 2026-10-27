import R1Z.PV_CBL_SplitBounds
namespace R1Z.PV_CBL_SplitArithmetic
set_option autoImplicit false

theorem tail_lt (len size : Nat) (hs : 0<size) : len%size<size := Nat.mod_lt len hs

theorem no_blocks (len size : Nat) (h : len<size) : len/size=0 := Nat.div_eq_of_lt h

theorem exact_blocks (count size : Nat) (hs : 0<size) : (count*size)/size=count :=
  Nat.mul_div_cancel count hs

theorem exact_tail (count size : Nat) : (count*size)%size=0 := by simp

theorem block_count_step (len size : Nat) (hs : 0<size) :
    (len+size)/size=len/size+1 := by omega

#print axioms tail_lt
#print axioms no_blocks
#print axioms exact_blocks
#print axioms exact_tail
#print axioms block_count_step
end R1Z.PV_CBL_SplitArithmetic

import R1Z.PV_CBL_SplitBounds
namespace R1Z.PV_CBL_SplitModel
set_option autoImplicit false

/-- Pure list specification for the reference's byte-copy loops, not yet
an extracted-source binding for op209. -/
def block {T : Type} (src : List T) (size i : Nat) : List T :=
  (src.drop (i*size)).take size

def tail {T : Type} (src : List T) (size : Nat) : List T :=
  src.drop ((src.length/size)*size)

theorem block_length {T : Type} (src : List T) (size i : Nat)
    (hi : i<src.length/size) : (block src size i).length=size := by
  have h : (i+1)*size≤src.length := le_trans
    (Nat.mul_le_mul_right size (by omega)) (Nat.div_mul_le_self _ _)
  have hsum : i*size+size≤src.length := by
    simpa only [Nat.add_mul,Nat.one_mul] using h
  simp only [block,List.length_take,List.length_drop]
  rw [Nat.min_eq_left (by omega)]

theorem tail_length {T : Type} (src : List T) (size : Nat) :
    (tail src size).length=src.length%size := by
  simp only [tail,List.length_drop]
  have := PV_CBL_SplitBounds.consumed_and_tail src.length size
  omega

theorem zero_size_tail {T : Type} (src : List T) : tail src 0=src := by simp [tail]

#print axioms block
#print axioms tail
#print axioms block_length
#print axioms tail_length
#print axioms zero_size_tail
end R1Z.PV_CBL_SplitModel

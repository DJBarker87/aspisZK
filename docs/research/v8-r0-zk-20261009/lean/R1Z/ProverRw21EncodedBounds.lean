import R1Z.ProverRw21FlatSequence
set_option autoImplicit false
namespace R1Z.ProverRw21EncodedBounds
open Aeneas Aeneas.Std
abbrev W := ProverRw21FlatOutput.W

theorem successor (values : Slice W) (i : Usize) (h : i.val<values.val.length) :
    (Usize.wrapping_add i 1#usize).val=i.val+1 := by
  rw [Usize.wrapping_add_val_eq]
  change (i.val+1) % UScalar.size .Usize = i.val+1
  apply Nat.mod_eq_of_lt
  have sized := (Slice.len values).hSize
  have sizedval : (Slice.len values).val=values.val.length := rfl
  omega

theorem step_capacity (values : Slice W) (out : alloc.vec.Vec U8) (i : Usize)
    (h : i.val<values.val.length)
    (bound : out.length+32*(values.length-i.val)≤Usize.max) : out.length+32≤Usize.max := by
  have : 1≤values.length-i.val := by exact Nat.sub_pos_of_lt h
  omega

theorem remaining (n i : Nat) (h : i<n) : 32*(n-i)=32+32*(n-(i+1)) := by omega

#print axioms successor
#print axioms step_capacity
#print axioms remaining
end R1Z.ProverRw21EncodedBounds

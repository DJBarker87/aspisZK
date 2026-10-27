import Port4B_NativeLeaf
set_option autoImplicit false
namespace AspisR1.JGk_TX2_LeafPush
open Aeneas Aeneas.Std Result MultiproofConeRef

def push (s : reference.Scratch) (index : U32) (leaf : Array U8 32#usize)
    (room : s.n.val<16) : reference.Scratch :=
  {s with idx:=s.idx.set s.n index,val:=s.val.set s.n leaf,n:=UScalar.ofNat (s.n.val+1) (by scalar_tac)}

theorem step (s : reference.Scratch) (index : U32) (leaf : Array U8 32#usize)
    (room : s.n.val<16) (fresh : ¬(0<s.n.val ∧ s.idx.val[s.n.val-1]! = index)) :
    reference.leaf_step s index leaf=ok (some (push s index leaf room)) := by
  rw [MultiproofConeLeafContent.step_exact s index leaf room]
  simp only [MultiproofConeLeafContent.next,if_neg fresh,push]
#print axioms step

theorem last (s : reference.Scratch) (index : U32) (leaf : Array U8 32#usize)
    (room : s.n.val<16) : (push s index leaf room).idx.val[s.n.val]! = index := by
  apply UScalar.eq_of_val_eq
  have eq := MultiproofConePhysicalLive.write_cell s s.n index leaf s.«at» room s.n.val room
  simpa only [push,MultiproofConePhysicalLive.cell,if_pos rfl,ite_true] using congrArg Prod.fst eq
#print axioms last

end AspisR1.JGk_TX2_LeafPush

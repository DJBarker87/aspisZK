import NDL_MultiproofAccess
set_option autoImplicit false
noncomputable section
namespace NDL_MultiproofConsumer
open Aeneas Aeneas.Std Result MultiproofConeRef

/-- One occupied binary source step using the SAME indexed input arrays and
actual source writer. Helper replacement is local; every sibling/loop/error
continuation stays the actual adopted definition. -/
theorem occupied_step {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (physical : Slice U8) (s : reference.Scratch) (i w ni : Usize)
    (index next : U32) (left right : Array U8 32#usize)
    (read : NDD_Reference.index_ref s.idx i=ok index)
    (first : Array.index_usize s.val i=ok left)
    (increment : i+1#usize=ok ni) (active : ni<s.n)
    (readNext : NDD_Reference.index_ref s.idx ni=ok next)
    (paired : next=index^^^1#u32)
    (second : Array.index_usize s.val ni=ok right) :
    reference.binary_step D hash s physical i w = (do
      let next ← i+2#usize
      reference.write_parent D hash s left right next s.«at» index w) := by
  rw [NDD_LeafRefs.index] at read readNext
  simp only [reference.binary_step,read,first,increment,bind_tc_ok,if_pos active,
    readNext,paired,if_pos,second]

#print axioms occupied_step
end NDL_MultiproofConsumer
end

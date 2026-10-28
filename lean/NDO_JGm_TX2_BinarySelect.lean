import NDO_JGk_TX2_ParentWrite
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_BinarySelect
open Aeneas Aeneas.Std Result MultiproofConeRef

theorem pair {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (nodes : Slice U8) (i w ni ni2 : Usize)
    (index : U32) (left right : Array U8 32#usize)
    (ri : Array.index_usize s.idx i=ok index)
    (rv : Array.index_usize s.val i=ok left)
    (inc : i+1#usize=ok ni) (more : ni<s.n)
    (rn : Array.index_usize s.idx ni=ok (index ^^^ 1#u32))
    (rr : Array.index_usize s.val ni=ok right)
    (inc2 : i+2#usize=ok ni2) :
    reference.binary_step D hash s nodes i w=
      reference.write_parent D hash s left right ni2 s.«at» index w := by
  simp only [reference.binary_step,ri,rv,inc,bind_tc_ok,if_pos more,rn,lift,if_true,rr,inc2]
#print axioms pair

/-- Only the input reads and the pure occupied-pair test are simplified here.
The external path still executes its actual range/read32/cursor operations. -/
theorem external {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (nodes : Slice U8) (i w ni : Usize)
    (index : U32) (value : Array U8 32#usize)
    (ri : Array.index_usize s.idx i=ok index)
    (rv : Array.index_usize s.val i=ok value)
    (inc : i+1#usize=ok ni)
    (unpaired : ∀ h : ni<s.n, ∃ other, Array.index_usize s.idx ni=ok other ∧ other≠index ^^^ 1#u32) :
    reference.binary_step D hash s nodes i w=
      (do let remaining ← Slice.len nodes-s.«at»
          if remaining<32#usize then ok (.Stop s)
          else
            let cursor ← s.«at»+32#usize
            let view ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
              nodes {start:=s.«at»,«end»:=cursor}
            let sibling ← reference.read32 view
            if index &&& 1#u32=0#u32 then
              reference.write_parent D hash s value sibling ni cursor index w
            else reference.write_parent D hash s sibling value ni cursor index w) := by
  simp only [reference.binary_step,ri,rv,inc,bind_tc_ok]
  by_cases more : ni<s.n
  · obtain ⟨other,read,ne⟩ := unpaired more
    simp only [if_pos more,read,bind_tc_ok,lift,if_neg ne]
  · simp only [if_neg more,lift,bind_tc_ok]
#print axioms external
end AspisR1.JGm_TX2_BinarySelect
end

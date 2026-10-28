import NDO_JGm_TX2_BinarySelect
import NDO_JGm_TX2_Scalar
import MultiproofConeSlices
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_ExternalRun
open Aeneas Aeneas.Std Result MultiproofConeRef

theorem source {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (nodes : Slice U8) (i w ni cursor remaining : Usize)
    (index : U32) (value sibling : Array U8 32#usize)
    (ri : Array.index_usize s.idx i=ok index)
    (rv : Array.index_usize s.val i=ok value)
    (inc : i+1#usize=ok ni)
    (unpaired : ∀ h : ni<s.n, ∃ other, Array.index_usize s.idx ni=ok other ∧ other≠index ^^^ 1#u32)
    (sub : Slice.len nodes-s.«at»=ok remaining) (room : ¬remaining<32#usize)
    (advance : s.«at»+32#usize=ok cursor)
    (order : s.«at».val≤cursor.val) (bound : cursor.val≤nodes.val.length)
    (read : reference.read32 (MultiproofConeSlices.sub nodes s.«at» cursor)=ok sibling) :
    reference.binary_step D hash s nodes i w=
      if index &&& 1#u32=0#u32 then
        reference.write_parent D hash s value sibling ni cursor index w
      else reference.write_parent D hash s sibling value ni cursor index w := by
  rw [JGm_TX2_BinarySelect.external D hash s nodes i w ni index value ri rv inc unpaired]
  simp only [sub,bind_tc_ok,if_neg room,advance,MultiproofConeSlices.range_total nodes s.«at» cursor order bound,read]
#print axioms source
end AspisR1.JGm_TX2_ExternalRun
end

import NKV_PaddingInstall
import Port4B_Padding
import RecordPayloadPartition
set_option autoImplicit false
noncomputable section
namespace NKV_PaddingChunks
open Aeneas Aeneas.Std Result AspisR1
open AspisV8R19.DuplexFrames
abbrev HashState := AspisV8R19.SourceDuplexStep.State

theorem total (padding : Slice U8) :
 ∃ ce,core.slice.Slice.chunks_exact padding 8#usize=ok ce ∧
   ∀ chunk∈ce.chunks,chunk.val.length=8 := by
 unfold core.slice.Slice.chunks_exact
 split
 · refine ⟨_,rfl,?_⟩
   intro chunk member
   obtain ⟨raw,member,same⟩:=List.mem_map.mp member
   subst chunk
   exact RecordPayloadPartition.chunks_full_length 8 (by decide) padding.val raw.val raw.property
 · next bad => simp at bad

/-- Native one-word predicate plus Lean iterator induction produces a complete
return on arbitrary padding, including short-circuit rejection. -/
theorem scan (H : Bytes → HashState) (padding : Slice U8) :
 ∃ ce after verdict,core.slice.Slice.chunks_exact padding 8#usize=ok ce ∧
 (NKV_ConcreteChildren.ops H).op0 (core.iter.traits.iterator.IteratorChunksExact U8)
   (NKV_PaddingInstall.predicate H) ce ()=ok (verdict,after) ∧
 verdict=(NKB_AnyModel.scan ce.chunks).1 := by
 obtain ⟨ce,run,full⟩:=total padding
 exact ⟨ce,{chunks:=(NKB_AnyModel.scan ce.chunks).2,remainder:=ce.remainder},
   (NKB_AnyModel.scan ce.chunks).1,run,NKV_PaddingInstall.total H ce.chunks ce.remainder full,rfl⟩

set_option pp.proofs false
#print total
#print scan
#print axioms total
#print axioms scan
end NKV_PaddingChunks
end

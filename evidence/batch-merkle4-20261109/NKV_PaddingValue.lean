import NKV_PaddingChunks
import NCM_PaddingBytes
set_option autoImplicit false
noncomputable section
namespace NKV_PaddingValue
open Aeneas Aeneas.Std Result AspisR1
open AspisV8R19.DuplexFrames
abbrev HashState := AspisV8R19.SourceDuplexStep.State

/-- The real installed any callback, original aligned bytes and mathematical
padding guard agree on BOTH outcomes, with the first-stop iterator retained. -/
theorem source (H : Bytes → HashState) (padding : Slice U8) (words : Nat)
 (length : padding.val.length=8*words) :
 ∃ ce after,core.slice.Slice.chunks_exact padding 8#usize=ok ce ∧
 (NKV_ConcreteChildren.ops H).op0 (core.iter.traits.iterator.IteratorChunksExact U8)
   (NKV_PaddingInstall.predicate H) ce ()=
 ok (!MultiproofConePadding.scan words (MultiproofConeCanonical.bytesOf padding.val),after) := by
 obtain ⟨ce,constructed,full⟩:=NKV_PaddingChunks.total padding
 have equivalent : (NKB_AnyModel.scan ce.chunks).1=false ↔
     MultiproofConePadding.scan words (MultiproofConeCanonical.bytesOf padding.val)=true := by
   rw [NKB_AnyModel.false_iff ce.chunks full,NCM_PaddingBytes.scan padding words length]
   simp only [List.all_eq_true,beq_iff_eq]
   exact NCM_PaddingCover.zero padding ce constructed (by omega)
 have value : (NKB_AnyModel.scan ce.chunks).1=
     !MultiproofConePadding.scan words (MultiproofConeCanonical.bytesOf padding.val) := by
   cases left : (NKB_AnyModel.scan ce.chunks).1 <;>
     cases right : MultiproofConePadding.scan words (MultiproofConeCanonical.bytesOf padding.val) <;> simp_all
 refine ⟨ce,{chunks:=(NKB_AnyModel.scan ce.chunks).2,remainder:=ce.remainder},constructed,?_⟩
 rw [NKV_PaddingInstall.total H ce.chunks ce.remainder full,value]

set_option pp.proofs false
#print source
#print axioms source
end NKV_PaddingValue
end

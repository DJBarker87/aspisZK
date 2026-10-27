import JGm_TX2_PaddingScan
import JGu_Padding0
import JGu_Padding1
import JGu_Padding2
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGu_PaddingScan
open Aeneas Aeneas.Std Result
theorem source {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X)
    (padding : Slice U8) (bytes : padding.val=List.replicate 256 0#u8)
    (ce : core.slice.iter.ChunksExact U8)
    (chunks : core.slice.Slice.chunks_exact padding 8#usize=ok ce) :
    (Port3_BatchStd.install Port4B_Install.leaves).op0
      (core.iter.traits.iterator.IteratorChunksExact U8)
      (Port3_NativeBatchBody.verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool
        (Port3_BatchStd.install Port4B_Install.leaves) D) ce ()=
        ok (false,{chunks:=[],remainder:=ce.remainder}) := by
  apply JGm_TX2_AnyFalse.source
  intro chunk mem
  unfold core.slice.Slice.chunks_exact at chunks
  split at chunks
  next positive =>
    cases Result.ok.inj chunks
    obtain ⟨c,_,eq⟩ := List.mem_map.mp mem
    rcases c with ⟨c,hc⟩
    have member : c∈(List.toChunksExact 8 (by decide) padding.val).1 := hc
    rw [bytes,show 256=8*32 from rfl,JGm_TX2_PaddingScan.chunk_replicate] at member
    have cb := List.eq_of_mem_replicate member
    apply JGm_TX2_PaddingScan.predicate D
    simpa only [←eq] using cb
  next bad => simp at bad
#print axioms source
theorem calls {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X)
    (padding : Slice U8) (bytes : padding.val=List.replicate 256 0#u8) :
    ∃ ce after, core.slice.Slice.chunks_exact padding 8#usize=ok ce ∧
    (Port3_BatchStd.install Port4B_Install.leaves).op0
      (core.iter.traits.iterator.IteratorChunksExact U8)
      (Port3_NativeBatchBody.verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool
        (Port3_BatchStd.install Port4B_Install.leaves) D) ce ()=ok (false,after) := by
  have exists_chunks : ∃ ce, core.slice.Slice.chunks_exact padding 8#usize=ok ce := by
    unfold core.slice.Slice.chunks_exact
    split
    next positive => exact ⟨_,rfl⟩
    next bad => simp at bad
  obtain ⟨ce,read⟩ := exists_chunks
  exact ⟨ce,_,read,source D padding bytes ce read⟩
#print axioms calls

end AspisR1.JGu_PaddingScan
end

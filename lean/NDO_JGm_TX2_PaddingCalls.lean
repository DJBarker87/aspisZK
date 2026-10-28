import NDO_JGm_TX2_PaddingScan
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_PaddingCalls
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2

theorem source {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X)
    (padding : Slice U8) (bytes : padding.val=List.replicate 288 0#u8) :
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
  exact ⟨ce,_,read,JGm_TX2_PaddingScan.source D padding bytes ce read⟩
#print axioms source

def padding0 : Slice U8 := Slice.drop JGh_TX2_NodeViews.nodes0 5216#usize
def padding1 : Slice U8 := Slice.drop JGh_TX2_NodeViews.nodes1 5216#usize
def padding2 : Slice U8 := Slice.drop JGh_TX2_NodeViews.nodes2 4512#usize

theorem bytes0 : padding0.val=List.replicate 288 0#u8 := JGk_TX2_Padding0.source
#print axioms bytes0
theorem bytes1 : padding1.val=List.replicate 288 0#u8 := JGk_TX2_Padding1.source
#print axioms bytes1
theorem bytes2 : padding2.val=List.replicate 288 0#u8 := JGk_TX2_Padding2.source
#print axioms bytes2
end AspisR1.JGm_TX2_PaddingCalls
end

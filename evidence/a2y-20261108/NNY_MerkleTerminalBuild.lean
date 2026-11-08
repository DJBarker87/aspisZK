import NNY_MerkleTerminalFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNY_MerkleTerminalBuild
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeBatchBody NKV_StepErasure NKV_LoopTransport
theorem bind_ok {A B : Type} (m : Result A) (k : A → Result B) (x : A) (out : B)
 (hm : m=ok x) (hk : k x=ok out) : (do let a ← m; k a)=ok out := by
 rw [hm]
 exact hk

theorem constructed (base : Ops) (D : aspis_core.digest.Digest32 Unit)
 (proof : Slice U8) (root : Array U8 32#usize) (slot d : Usize)
 (idx outIdx : Indices) (val outVal : Values)
 (front : Slice U32) (count cap : Usize) (nodes padding supplied : Slice U8)
 (ce after : core.slice.iter.ChunksExact U8)
 (frontRead : core.array.Array.index (core.ops.index.IndexSlice
  (core.slice.index.SliceIndexRangeToUsizeSlice U32)) idx {«end»:=d}=ok front)
 (countRead : base.op11 multiproof.Arity.Two front=ok (some count))
 (nodeRead : base.op3 proof slot=ok nodes)
 (capRead : Array.index_usize (Array.make 6#usize
  [146#usize,146#usize,128#usize,172#usize,172#usize,150#usize]) slot=ok cap)
 (fit : ¬count > cap)
 (paddingRead : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
  nodes {start:=Usize.wrapping_mul 32#usize count}=ok padding)
 (chunksRead : core.slice.Slice.chunks_exact padding 8#usize=ok ce)
 (scanRead : (Port3_BatchStd.install base).op0 (core.iter.traits.iterator.IteratorChunksExact U8)
  (verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool
   (Port3_BatchStd.install base) D) ce ()=ok (false,after))
 (prefixRead : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
  nodes {«end»:=Usize.wrapping_mul 32#usize count}=ok supplied)
 (verifyRead : base.op10 D () multiproof.Arity.Two root idx val d supplied=ok (true,outIdx,outVal)) :
 NNY_MerkleTerminalFrame.code base D proof root () slot d idx val=ok (.done (outIdx,outVal,some (.Ok ()))) := by
 unfold NNY_MerkleTerminalFrame.code
 refine bind_ok _ _ front _ frontRead ?_
 refine bind_ok _ _ (some count) _ countRead ?_
 refine bind_ok _ _ (.Ok count) _ rfl ?_
 refine bind_ok _ _ (.Continue count) _ rfl ?_
 refine bind_ok _ _ nodes _ nodeRead ?_
 refine bind_ok _ _ _ _ rfl ?_
 refine bind_ok _ _ cap _ capRead ?_
 rw [if_neg fit]
 refine bind_ok _ _ _ _ rfl ?_
 refine bind_ok _ _ padding _ paddingRead ?_
 refine bind_ok _ _ ce _ chunksRead ?_
 refine bind_ok _ _ (false,after) _ scanRead ?_
 refine bind_ok _ _ _ _ rfl ?_
 refine bind_ok _ _ supplied _ prefixRead ?_
 refine bind_ok _ _ (true,outIdx,outVal) _ verifyRead ?_
 rfl
#print axioms bind_ok
#print axioms constructed
end AspisR1.NNY_MerkleTerminalBuild
end

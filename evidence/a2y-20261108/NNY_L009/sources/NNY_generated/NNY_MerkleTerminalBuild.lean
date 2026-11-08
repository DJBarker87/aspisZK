import NNY_MerkleTerminalFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNY_MerkleTerminalBuild
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeBatchBody NKV_StepErasure NKV_LoopTransport
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
 rw [frontRead]
 simp only [bind_tc_ok,NNY_MerkleTerminalFrame.count_slot]
 rw [countRead]
 simp only [Port3_BatchStd.okOr,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
 simp only [NNY_MerkleTerminalFrame.node_slot,nodeRead,bind_tc_ok]
 have capSlot : (Port3_BatchStd.install base).op12 = ok (Array.make 6#usize
  [146#usize,146#usize,128#usize,172#usize,172#usize,150#usize]) := rfl
 simp only [capSlot,capRead,bind_tc_ok,if_neg fit,lift]
 rw [paddingRead,chunksRead]
 simp only [bind_tc_ok]
 rw [scanRead]
 simp only [bind_tc_ok,Bool.false_eq_true,if_false]
 rw [prefixRead]
 simp only [bind_tc_ok]
 rw [NNY_MerkleTerminalFrame.verify_slot,verifyRead]
 rfl
#print axioms constructed
end AspisR1.NNY_MerkleTerminalBuild
end

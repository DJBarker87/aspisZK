import Port4B_Rejection

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_NativeReject
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeBatchCalls (Indices Values)

/-- Source-local failure path of the ACTUAL installed loop body. The only
child hypotheses are the physical index-prefix read and node-count failure;
no whole-loop result, batch result or oracle-log equality is assumed. -/
theorem missing_count (leaves : Port3_NativeBatchBody.Ops) {H : Type}
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (proof : Slice U8) (root : Array U8 32#usize) (tree lo n s d : Usize)
    (keys : Array U64 16#usize) (idx : Indices) (val : Values) (prefixIdx : Slice U32)
    (read : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice U32)) idx { «end» := d } = ok prefixIdx)
    (count : leaves.op11 Port3_NativeBatchBody.multiproof.Arity.Two prefixIdx = ok none) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install leaves) D proof root tree hash lo n s keys idx val d n =
      ok (.done (idx,val,none)) := by
  simp only [Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body,
    lt_self_iff_false,if_false,read,bind_tc_ok,Port3_BatchStd.install,count,
    Port3_BatchStd.okOr,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

/-- Nonzero physical padding takes the actual installed emitted exit with
no pending Rust error. The count, capacity, suffix and scan are LOCAL reads;
no complete slot/loop success or observation is an input. -/
theorem nonzero_padding (leaves : Port3_NativeBatchBody.Ops) {H : Type}
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (proof : Slice U8) (root : Array U8 32#usize) (tree lo n s d : Usize)
    (keys : Array U64 16#usize) (idx : Indices) (val : Values)
    (prefixIdx : Slice U32) (count cap scaled : Usize) (nodes padding : Slice U8)
    (read : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice U32)) idx { «end» := d } = ok prefixIdx)
    (counted : leaves.op11 Port3_NativeBatchBody.multiproof.Arity.Two prefixIdx = ok (some count))
    (slotRead : leaves.op3 proof s = ok nodes)
    (capRead : Array.index_usize
      (Array.make 6#usize [146#usize,146#usize,128#usize,172#usize,172#usize,150#usize]) s = ok cap)
    (bound : ¬ count > cap)
    (multiply : lift (Usize.wrapping_mul 32#usize count) = ok scaled)
    (suffixRead : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeFromUsizeSlice U8) nodes { start := scaled } = ok padding)
    (nonzero : ∃ ce after, core.slice.Slice.chunks_exact padding 8#usize = ok ce ∧
      (Port3_BatchStd.install leaves).op0
        (core.iter.traits.iterator.IteratorChunksExact U8)
        (Port3_NativeBatchBody.verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool
          (Port3_BatchStd.install leaves) D) ce () = ok (true,after)) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install leaves) D proof root tree hash lo n s keys idx val d n =
      ok (.done (idx,val,none)) := by
  obtain ⟨ce,after,chunks,scan⟩ := nonzero
  unfold Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
  simp only [lt_self_iff_false,if_false,read,bind_tc_ok]
  simp only [Port3_BatchStd.install] at scan ⊢
  simp only [counted,bind_tc_ok,Port3_BatchStd.okOr,core.result.Result.Insts.CoreOpsTry.branch]
  simp only [slotRead,bind_tc_ok,capRead,if_neg bound,multiply,suffixRead,chunks,scan,if_true]

#print axioms missing_count
#print axioms nonzero_padding
end AspisR1.Port4B_NativeReject
end

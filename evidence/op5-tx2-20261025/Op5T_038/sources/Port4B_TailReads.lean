import Port4B_SlotInstall

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_TailReads
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeBatchCalls (Indices Values)

/-- All actual accepted terminal reads, including the COMPLETE padding scan.
The root and arrays passed to the verifier are precisely the leaf-phase state. -/
theorem reads (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D : aspis_core.digest.Digest32 X) (hash : X)
    (proof : Slice U8) (root : Array U8 32#usize) (kind lo n slot d : Usize)
    (keys : Array U64 16#usize) (idx outIdx : Indices) (val outVal : Values)
    (accepted : Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install base) D proof root kind hash lo n slot keys idx val d n=
      ok (.done (outIdx,outVal,some (.Ok ())))) :
    ∃ (front : Slice U32) (count cap : Usize) (nodes padding supplied : Slice U8)
      (ce after : core.slice.iter.ChunksExact U8),
      core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32))
        idx {«end»:=d}=ok front ∧
      base.op11 Port3_NativeBatchBody.multiproof.Arity.Two front=ok (some count) ∧
      base.op3 proof slot=ok nodes ∧
      Array.index_usize (Array.make 6#usize [146#usize,146#usize,128#usize,172#usize,172#usize,150#usize])
        slot=ok cap ∧ ¬ count>cap ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
        nodes {start:=Usize.wrapping_mul 32#usize count}=ok padding ∧
      core.slice.Slice.chunks_exact padding 8#usize=ok ce ∧
      (Port3_BatchStd.install base).op0 (core.iter.traits.iterator.IteratorChunksExact U8)
        (Port3_NativeBatchBody.verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool
          (Port3_BatchStd.install base) D) ce ()=ok (false,after) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
        nodes {«end»:=Usize.wrapping_mul 32#usize count}=ok supplied ∧
      base.op10 D hash Port3_NativeBatchBody.multiproof.Arity.Two root idx val d supplied=
        ok (true,outIdx,outVal) := by
  unfold Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body at accepted
  simp only [lt_self_iff_false,if_false,Port3_BatchStd.install] at accepted
  obtain ⟨front,frontRead,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
  obtain ⟨o,countRead,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
  cases o with
  | none => cases accepted
  | some count =>
    simp only [Port3_BatchStd.okOr,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] at accepted
    obtain ⟨nodes,nodeRead,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
    obtain ⟨cap,capRead,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
    by_cases large : count>cap
    · simp only [if_pos large] at accepted;cases accepted
    · simp only [if_neg large,lift,bind_tc_ok] at accepted
      obtain ⟨padding,paddingRead,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
      obtain ⟨ce,chunksRead,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
      obtain ⟨⟨nonzero,after⟩,scanRead,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
      cases nonzero with
      | true => cases accepted
      | false =>
        try simp only [Bool.false_eq_true,if_false] at accepted
        obtain ⟨supplied,prefixRead,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
        obtain ⟨⟨verified,returnedIdx,returnedVal⟩,verifyRead,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
        cases verified with
        | false => cases accepted
        | true =>
          have equal := ControlFlow.done.inj (Result.ok.inj accepted)
          simp only [Prod.mk.injEq] at equal
          rcases equal with ⟨sameIdx,sameVal,_⟩
          exact ⟨front,count,cap,nodes,padding,supplied,ce,after,frontRead,countRead,nodeRead,
            capRead,large,paddingRead,chunksRead,scanRead,prefixRead,
            by simpa only [sameIdx,sameVal] using verifyRead⟩

#print axioms reads
end AspisR1.Port4B_TailReads
end

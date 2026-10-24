import Port4B_NativeReject

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_AcceptedTail
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeBatchCalls (Indices Values)

/-- Local observations forced by the actual successful terminal iteration.
The verifier consumes the same root and scratch, the checked count, and the
actual physical prefix. No independent verifier success is supplied. -/
theorem verify_call (leaves : Port3_NativeBatchBody.Ops) {H : Type}
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (proof : Slice U8) (root : Array U8 32#usize) (tree lo n slot d pos : Usize)
    (keys : Array U64 16#usize) (idx outIdx : Indices) (val outVal : Values)
    (halt : ¬ pos < n)
    (accepted : Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install leaves) D proof root tree hash lo n slot keys idx val d pos =
      ok (.done (outIdx,outVal,some (.Ok ())))) :
    ∃ (front : Slice U32) (count cap : Usize) (nodes supplied : Slice U8),
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice U32)) idx {«end»:=d} = ok front ∧
      leaves.op11 Port3_NativeBatchBody.multiproof.Arity.Two front = ok (some count) ∧
      leaves.op3 proof slot = ok nodes ∧
      Array.index_usize
        (Array.make 6#usize [146#usize,146#usize,128#usize,172#usize,172#usize,150#usize]) slot = ok cap ∧
      ¬ count > cap ∧
      (∃ scaled, lift (Usize.wrapping_mul 32#usize count) = ok scaled ∧
        core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
          nodes {«end»:=scaled} = ok supplied) ∧
      leaves.op10 D hash Port3_NativeBatchBody.multiproof.Arity.Two root idx val d supplied =
        ok (true,outIdx,outVal) := by
  unfold Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body at accepted
  simp only [if_neg halt,Port3_BatchStd.install] at accepted
  obtain ⟨front,hfront,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
  obtain ⟨o,hcount,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
  cases o with
  | none => cases accepted
  | some count =>
    simp only [Port3_BatchStd.okOr,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch] at accepted
    repeat' first
    | (solve | cases accepted)
    | uncase_result
    | head_reduce accepted
    | split at accepted
    all_goals
      rename_i verifyResult verifyOut verifyCall verified
      have equal := ControlFlow.done.inj (Result.ok.inj accepted)
      simp only [Prod.mk.injEq] at equal
      rcases equal with ⟨equalIdx,equalVal,_⟩
      refine ⟨_,_,_,_,_,hfront,hcount,by assumption,
        by assumption,by assumption,⟨_,rfl,by assumption⟩,?_⟩
      have same : verifyOut = (true,outIdx,outVal) :=
        Prod.ext verified (Prod.ext equalIdx equalVal)
      exact verifyCall.trans (congrArg Result.ok same)

#print axioms verify_call
end AspisR1.Port4B_AcceptedTail
end

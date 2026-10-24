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
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame]
  rfl

#print axioms missing_count
end AspisR1.Port4B_NativeReject
end

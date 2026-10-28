import NCT_DriverDomain
import NBA_QueryJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCU_PrefixTail
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
@[irreducible] def tail (ops : Ops) {H : Type}
    (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
    (public_bytes proof : Slice U8) (k : Usize) (hash : H)
    
    (val : verifier.Prepared)
    (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
  let r3 ← ops.op20 transport.Variant.S2
  let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
  match cf3 with
  | core.ops.control_flow.ControlFlow.Continue val1 =>
    verifier.mark none verifier.Phase.Prepare
    let i ← (compact.OFF_FOLDED_ROOT ops)
    let i1 ← (compact.OFF_ROUND1 ops)
    let s ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
        { start := i, «end» := i1 }
    let r4 ←
      core.array.TryFromArrayCopySlice.try_from 32#usize
        core.marker.CopyU8 s
    let folded_root ←
      core.result.Result.unwrap core.fmt.DebugTryFromSliceError r4
    let r5 ←
      ops.op6 aspis_coredigestDigest32Inst
        proof val folded_root 0#usize hash
    let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
    match cf4 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      verifier.mark none (verifier.Phase.Merkle 0#usize)
      let r6 ← ops.op19 val.queries 0#usize k
      let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
      match cf5 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let s1 := alloc.vec.Vec.deref val1.weights
        let r7 ← ops.op18 s1
        let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r7
        match cf6 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let r8 ←
            ops.op7 proof val val1 g1 none val2
              val3 k
          let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r8
          match cf7 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            let (a, pending) := val4
            let (s2, deref_mut_back) ←
              lift (alloc.vec.Vec.deref_mut a.weights)
            let s3 ← ops.op17 pending s2
            let v := deref_mut_back s3
            ok (core.result.Result.Ok (val, { a with weights := v }))
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (verifier.Prepared × verifier.Accumulator) (core.convert.FromSame
              verifier.Error) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (verifier.Prepared × verifier.Accumulator) (core.convert.FromSame
            verifier.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (verifier.Prepared × verifier.Accumulator) (core.convert.FromSame verifier.Error)
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (verifier.Prepared × verifier.Accumulator) (core.convert.FromSame verifier.Error)
        residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (verifier.Prepared × verifier.Accumulator) (core.convert.FromSame verifier.Error)
      residual
@[irreducible] def finish (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub proof : Slice U8) (hash : H)
    (pre : Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error)) :
    Result (core.result.Result (alloc.vec.Vec U8) verifier.Error) := do
  let r ← pre
  match r with
  | .Err error => ok (.Err error)
  | .Ok (p,a) => do
    let bytes ← ops.op16 D p a proof pub hash
    ok (.Ok bytes)

attribute [local irreducible] Tx1Reachability.afterPrepare

theorem factor (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub proof : Slice U8) (split : Usize) (hash : H)
    (p : verifier.Prepared) (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    Tx1Reachability.afterPrepare ops D pub proof split hash none p g =
      finish ops D pub proof hash (tail ops D pub proof split hash p g) := by
  unfold Tx1Reachability.afterPrepare tail finish
  repeat' first
  | rfl
  | (fail_if_no_progress simp only [bind_assoc_eq,bind_tc_ok,verifier.mark,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from,Aeneas.Std.uncurry])
  | (apply NBA_QueryJoin.bind_same; intro x)
  | casesm (core.result.Result _ _)
  | casesm (_ × _)
  | split
#print axioms factor
end AspisR1.NCU_PrefixTail
end

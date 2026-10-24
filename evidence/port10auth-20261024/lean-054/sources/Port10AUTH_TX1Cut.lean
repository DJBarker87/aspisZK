import Port9OR_FirstBatch

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port10AUTH_TX1Cut
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def afterBatch {Hash : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 Hash)
    (public_bytes proof : Slice U8) (k : Usize) (hash : Hash)
    (obs : Option (verifier.Phase → Result Unit))
    (val : verifier.Prepared) (val1 : verifier.Accumulator)
    (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (r5 : core.result.Result Unit verifier.Error) : Code (core.result.Result (alloc.vec.Vec U8) verifier.Error) := do
  let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
  match cf4 with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    VTop_Flow.traceEffects.op13 obs (AdapterRw.aspis_r1_cost_probe.verifier.Phase.Merkle 0#usize)
    let r6 ← VTop_Flow.traceEffects.op11 val.queries 0#usize k
    let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
    match cf5 with
    | core.ops.control_flow.ControlFlow.Continue val2 =>
      let s1 := alloc.vec.Vec.deref val1.weights
      let r7 ← VTop_Flow.traceEffects.op10 s1
      let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r7
      match cf6 with
      | core.ops.control_flow.ControlFlow.Continue val3 =>
        let r8 ←
          VTop_Flow.traceEffects.op6 proof val val1 g1 obs val2
            val3 k
        let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r8
        match cf7 with
        | core.ops.control_flow.ControlFlow.Continue val4 =>
          let (a, pending) := val4
          let (s2, deref_mut_back) ←
            lift (alloc.vec.Vec.deref_mut a.weights)
          let s3 ← VTop_Flow.traceEffects.op9 pending s2
          let v := deref_mut_back s3
          let bytes ←
            VTop_Flow.traceEffects.op8 aspis_coredigestDigest32Inst val
              { a with weights := v } proof public_bytes hash
          VTop_Flow.traceEffects.op13 obs AdapterRw.aspis_r1_cost_probe.verifier.Phase.CheckpointWrite
          pure (core.result.Result.Ok bytes)
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec Std.U8) (core.convert.FromSame
            verifier.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame
          verifier.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
        residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
      residual

def code {Hash : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 Hash)
    (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (public_bytes proof : Slice U8) (k : Usize) (hash : Hash)
    (obs : Option (verifier.Phase → Result Unit)) : Code (core.result.Result (alloc.vec.Vec U8) verifier.Error) := do
  let i ← VTop_Flow.traceEffects.op16
  if k != i
  then pure (core.result.Result.Err AdapterRw.aspis_r1_cost_probe.verifier.Error.Parse)
  else
    let r ← VTop_Flow.traceEffects.op3 proof
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let r1 ← VTop_Flow.traceEffects.op4 proof
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        VTop_Flow.traceEffects.op13 obs AdapterRw.aspis_r1_cost_probe.verifier.Phase.Parsed
        let we ← VTop_Flow.traceEffects.op1
        let g := Array.repeat 29#usize we
        let (r2, g1) ←
          VTop_Flow.traceEffects.op7 aspis_coredigestDigest32Inst public1 proof
            hash obs g
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val =>
          let r3 ← VTop_Flow.traceEffects.op12 AspisR1Stage2.transport.Variant.S2
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val1 =>
            VTop_Flow.traceEffects.op13 obs AdapterRw.aspis_r1_cost_probe.verifier.Phase.Prepare
            let i1 ← VTop_Flow.traceEffects.op15
            let i2 ← VTop_Flow.traceEffects.op14
            let s ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
                { start := i1, «end» := i2 }
            let r4 ←
              core.array.TryFromArrayCopySlice.try_from 32#usize
                core.marker.CopyU8 s
            let folded_root ←
              VTop_Flow.traceEffects.unwrap32 r4
            VTop_Trace.perform (.op5 aspis_coredigestDigest32Inst proof val folded_root 0#usize hash) >>= fun r5 =>
              afterBatch aspis_coredigestDigest32Inst public_bytes proof k hash obs val val1 g1 r5
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
            residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual
theorem source {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (public_bytes proof : Slice U8) (k : Usize) (hash : Hash)
    (obs : Option (verifier.Phase → Result Unit)) :
    code D public1 public_bytes proof k hash obs=VTop_Flow.tx1 VTop_Flow.traceEffects D public1 public_bytes proof k hash obs := rfl

#print axioms source
end AspisR1.Port10AUTH_TX1Cut
end

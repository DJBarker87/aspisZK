import DrvC_FirstLibrary
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_FirstSyntax
open Aeneas Aeneas.Std Result
open DrvC_Installation Tx1Q_Carriers
local instance : MonadLift Result SdkC_Source.Code where
  monadLift := CheckpointBytes5Effect.liftResult

def stageTail {F C : Type} (c : Configuration F C) (pub proof : Slice U8) (k : Usize)
    (p : S.P) (g : Array S.E 29#usize) :
    SdkC_Source.Code (core.result.Result (alloc.vec.Vec U8) VTop_Stages.verifier.Error) :=
  let effects := DrvC_Effects.effects c
  do
  let r3 ← effects.op12 AspisR1Stage2.transport.Variant.S2
  let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
  match cf3 with
  | core.ops.control_flow.ControlFlow.Continue val1 =>
    effects.op13 none AdapterRw.aspis_r1_cost_probe.verifier.Phase.Prepare
    let i1 ← effects.op15
    let i2 ← effects.op14
    let s ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
        { start := i1, «end» := i2 }
    let r4 ←
      core.array.TryFromArrayCopySlice.try_from 32#usize
        core.marker.CopyU8 s
    let folded_root ←
      effects.unwrap32 r4
    let r5 ←
      effects.op5 (digest c)
        proof p folded_root 0#usize ()
    let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
    match cf4 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      effects.op13 none (AdapterRw.aspis_r1_cost_probe.verifier.Phase.Merkle 0#usize)
      let r6 ← effects.op11 p.queries 0#usize k
      let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
      match cf5 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let s1 := alloc.vec.Vec.deref val1.weights
        let r7 ← effects.op10 s1
        let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r7
        match cf6 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let r8 ←
            effects.op6 proof p val1 g none val2
              val3 k
          let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r8
          match cf7 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            let (a, pending) := val4
            let (s2, deref_mut_back) ←
              lift (alloc.vec.Vec.deref_mut a.weights)
            let s3 ← effects.op9 pending s2
            let v := deref_mut_back s3
            let bytes ←
              effects.op8 (digest c) p
                { a with weights := v } proof public_bytes ()
            effects.op13 none AdapterRw.aspis_r1_cost_probe.verifier.Phase.CheckpointWrite
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
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
      residual

def sourceTail {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (pub proof : Slice U8) (k : Usize)
    (p : Tx1Q_Carriers.C.P) (g : Array Tx1Q_Carriers.C.E 29#usize) :
    SdkC_Source.Code (core.result.Result (alloc.vec.Vec U8) AspisR1CurrentCaller.verifier.Error) :=
  let ops := currentInstalled c
  do
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
      SdkC_BatchSource.currentCode hashv proof p folded_root
    let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
    match cf4 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      verifier.mark none (verifier.Phase.Merkle 0#usize)
      let r6 ← ops.op19 p.queries 0#usize k
      let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
      match cf5 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let s1 := alloc.vec.Vec.deref val1.weights
        let r7 ← ops.op18 s1
        let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r7
        match cf6 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let r8 ←
            ops.op7 proof p val1 g none val2 val3 k
          let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r8
          match cf7 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            let (a, pending) := val4
            let (s2, deref_mut_back) ←
              lift (alloc.vec.Vec.deref_mut a.weights)
            let s3 ← ops.op17 pending s2
            let v := deref_mut_back s3
            let bytes ←
              GExp_FirstCode.writerCode p {a with weights := v} proof public_bytes
            verifier.mark none verifier.Phase.CheckpointWrite
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
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
      residual

end AspisR1.DrvC_FirstSyntax
end

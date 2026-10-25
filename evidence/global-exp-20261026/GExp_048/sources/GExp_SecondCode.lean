import GExp_ReaderCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_SecondCode
open Aeneas Aeneas.Std Result VTop_Stages
open CheckpointBytes5Effect (Code)
local instance : MonadLift Result Code where monadLift := CheckpointBytes5Effect.liftResult

def installed (base : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap) : Ops :=
  Port6CK_Reader.install (Op5T_Concrete.stage base) reserved unwrap

def common (base : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
  (D : aspis_core.digest.Digest32 Unit)
  (public_bytes : Slice Std.U8) (proof : Slice Std.U8)
  (checkpoint : Slice Std.U8) :
  Code (core.result.Result Unit verifier.Error)
  :=
  let ops := installed base reserved unwrap
  do
  let r ←
    GExp_ReaderCode.code reserved unwrap checkpoint proof public_bytes .S2
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (p, a) := val
    let i ← ops.op16
    if a.next != i
    then pure (core.result.Result.Err AdapterRw.aspis_r1_cost_probe.verifier.Error.Checkpoint)
    else
      let g ← ops.op17 29#usize p.gamma
      ops.op13 none AdapterRw.aspis_r1_cost_probe.verifier.Phase.CheckpointRead
      let i1 ← ops.op23
      let i2 ← ops.op22
      let s ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
          { start := i1, «end» := i2 }
      let o ← ops.op2 s
      let r1 ← ops.op0 o AdapterRw.aspis_r1_cost_probe.verifier.Error.Parse
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let i3 ← ops.op15
        let i4 ← ops.op14
        let s1 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
            { start := i3, «end» := i4 }
        let r2 ←
          core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8
            s1
        let folded_root ←
          ops.unwrap32 r2
        let r3 ←
          SdkC_BatchSource.stageCode hashv proof p folded_root
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          ops.op13 none (AdapterRw.aspis_r1_cost_probe.verifier.Phase.Merkle i)
          let r4 ← ops.op11 p.queries a.next 22#usize
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val2 =>
            let s2 := alloc.vec.Vec.deref a.weights
            let r5 ← ops.op10 s2
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue val3 =>
              let r6 ←
                ops.op6 proof p a g none val2 val3
                  22#usize
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue val4 =>
                let (a1, pending) := val4
                let (s3, deref_mut_back) ←
                  lift (alloc.vec.Vec.deref_mut a1.weights)
                let s4 ← ops.op9 pending s3
                let weights := deref_mut_back s4
                let s5 ← lift (Array.to_slice (Std.Array.empty Std.U8))
                let s6 ← lift (Array.to_slice (Std.Array.empty Std.U8))
                let s7 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
                    { start := i2, «end» := i3 }
                let i5 ← ops.op21
                let s8 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
                    { start := i4, «end» := i5 }
                let i6 ← ops.op20
                let s9 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
                    { start := i5, «end» := i6 }
                let s10 ← lift (Array.to_slice (Std.Array.empty Std.U8))
                ops.op19
                  {
                    variant := AspisR1Stage2.transport.Variant.S2,
                    semantic := s5,
                    y1 := s6,
                    inactive := val1,
                    round0 := s7,
                    folded_root := none,
                    round1 := s8,
                    final_message := s9,
                    query_bytes := s10
                  } p { a1 with weights } none
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  Unit (core.convert.FromSame verifier.Error) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                Unit (core.convert.FromSame verifier.Error) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Unit (core.convert.FromSame verifier.Error) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            Unit (core.convert.FromSame verifier.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame verifier.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame verifier.Error) residual

def code (base : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
  (D : aspis_core.digest.Digest32 Unit)
  (public_bytes : Slice Std.U8) (proof : Slice Std.U8)
  (checkpoint : Slice Std.U8) :
  Code (core.result.Result Unit verifier.Error)
  :=
  let ops := installed base reserved unwrap
  do
  let r ← ops.op3 proof
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    ops.op13 none AdapterRw.aspis_r1_cost_probe.verifier.Phase.Parsed
    common base reserved unwrap hashv D public_bytes proof checkpoint
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame verifier.Error) residual

end AspisR1.GExp_SecondCode
end

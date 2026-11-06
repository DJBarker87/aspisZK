import NKE_CommonCodec
set_option autoImplicit false
noncomputable section
namespace NKE_CommonProgram
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved

def run (weightReservation rawReservation : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (public_bytes : Slice Std.U8) (proof : Slice Std.U8)
  (checkpoint : Slice Std.U8) (hash : H)
  (obs : Option (verifier.Phase → Result Unit)) :
  NKE_Free.Program Event (core.result.Result Unit verifier.Error)
  := do
  let r ←
    NKE_Free.record (NKE_CommonCodec.resume checkpoint proof public_bytes)
      ((NJJ_Common.resume weightReservation) aspis_coredigestDigest32Inst checkpoint proof public_bytes
       AspisR1Stage2.transport.Variant.S2 hash)
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (p, a) := val
    if a.next != NHT_Constants.compact.SPLIT
    then ok (core.result.Result.Err AdapterRw.aspis_r1_cost_probe.verifier.Error.Checkpoint)
    else
      let g ← NKE_Free.record (NKE_CommonCodec.powers p.gamma) (NHT_PacketOps.powers 29#usize p.gamma)
      NHV_ReleaseOps.mark obs AdapterRw.aspis_r1_cost_probe.verifier.Phase.CheckpointRead
      let i ← NHT_Constants.compact.OFF_INACTIVE
      let i1 ← NHT_Constants.compact.OFF_ROUND0
      let s ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
          { start := i, «end» := i1 }
      let o ← NKE_Free.record (NKE_CommonCodec.inactive s) (NJC_ClosedCalls.inactive s)
      let r1 ← NHT_Constants.core.option.Option.ok_or o AdapterRw.aspis_r1_cost_probe.verifier.Error.Parse
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let i2 ← NHT_Constants.compact.OFF_FOLDED_ROOT
        let i3 ← NHT_Constants.compact.OFF_ROUND1
        let s1 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
            { start := i2, «end» := i3 }
        let r2 ←
          core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8
            s1
        let folded_root ←
          core.result.Result.unwrap core.fmt.DebugTryFromSliceError r2
        let r3 ←
          NKE_Free.record (NKE_CommonCodec.merkle proof p folded_root)
            (merkle aspis_coredigestDigest32Inst proof p folded_root 1#usize hash)
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          NHV_ReleaseOps.mark obs (AdapterRw.aspis_r1_cost_probe.verifier.Phase.Merkle NHT_Constants.compact.SPLIT)
          let r4 ← NKE_Free.record (NKE_CommonCodec.geometry p.queries a.next) (NJC_ClosedCalls.geometry p.queries a.next 22#usize)
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val2 =>
            let s2 := alloc.vec.Vec.deref a.weights
            let r5 ← NKE_Free.record (NKE_CommonCodec.pending s2) ((NJJ_Common.pending rawReservation) s2)
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue val3 =>
              let r6 ←
                NKE_Free.record (NKE_CommonCodec.query proof p a g val2 val3)
                  (NJJ_Common.query proof p a g obs val2 val3 22#usize)
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue val4 =>
                let (a1, pending) := val4
                let (s3, deref_mut_back) ←
                  lift (alloc.vec.Vec.deref_mut a1.weights)
                let s4 ← NKE_Free.record (NKE_CommonCodec.flush pending s3) (Port3_FlushInstall.flush pending s3)
                let weights := deref_mut_back s4
                let s5 ← lift (Array.to_slice (Std.Array.empty Std.U8))
                let s6 ← lift (Array.to_slice (Std.Array.empty Std.U8))
                let s7 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
                    { start := i1, «end» := i2 }
                let i4 ← NHT_Constants.compact.OFF_FINAL
                let s8 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
                    { start := i3, «end» := i4 }
                let i5 ← NHT_Constants.compact.OFF_OPENINGS
                let s9 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
                    { start := i4, «end» := i5 }
                let s10 ← lift (Array.to_slice (Std.Array.empty Std.U8))
                let finalView : verifier.View := {
                    variant := AspisR1Stage2.transport.Variant.S2,
                    semantic := s5,
                    y1 := s6,
                    inactive := val1,
                    round0 := s7,
                    folded_root := none,
                    round1 := s8,
                    final_message := s9,
                    query_bytes := s10
                  }
                let actual : verifier.Accumulator := {a1 with weights}
                NKE_Free.record (NKE_CommonCodec.finish finalView p actual) (finish finalView p actual obs)
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


end NKE_CommonProgram

import VTop_Flow
set_option autoImplicit false
noncomputable section
namespace AspisR1.VTop_SecondFlow
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_Flow
universe v

def tail {M : Type → Type v} [Monad M] [MonadLiftT Result M] (effects : Effects M)
    (proof : Slice U8) (p : verifier.Prepared) (obs : Option (verifier.Phase → Result Unit))
    (inactive : aspis_core.field.wide_exact.WideExact) (round0 folded round1 : Usize)
    (state : verifier.Accumulator × verifier.BatchedWeights) : M (core.result.Result Unit verifier.Error) := do
  let (a1, pending) := state
  let (s3, deref_mut_back) ←
    lift (alloc.vec.Vec.deref_mut a1.weights)
  let s4 ← effects.op9 pending s3
  let weights := deref_mut_back s4
  let s5 ← lift (Array.to_slice (Std.Array.empty Std.U8))
  let s6 ← lift (Array.to_slice (Std.Array.empty Std.U8))
  let s7 ←
    core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
      { start := round0, «end» := folded }
  let i5 ← effects.op21
  let s8 ←
    core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
      { start := round1, «end» := i5 }
  let i6 ← effects.op20
  let s9 ←
    core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
      { start := i5, «end» := i6 }
  let s10 ← lift (Array.to_slice (Std.Array.empty Std.U8))
  effects.op19
    {
      variant := AspisR1Stage2.transport.Variant.S2,
      semantic := s5,
      y1 := s6,
      inactive := inactive,
      round0 := s7,
      folded_root := none,
      round1 := s8,
      final_message := s9,
      query_bytes := s10
    } p { a1 with weights } obs

def common {M : Type → Type v} [Monad M] [MonadLiftT Result M] (effects : Effects M)
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (public_bytes : Slice Std.U8) (proof : Slice Std.U8)
  (checkpoint : Slice Std.U8) (hash : H)
  (obs : Option (verifier.Phase → Result Unit)) :
  M (core.result.Result Unit verifier.Error)
  := do
  let r ←
    effects.op18 aspis_coredigestDigest32Inst checkpoint proof public_bytes
      AspisR1Stage2.transport.Variant.S2 hash
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (p, a) := val
    let i ← effects.op16
    if a.next != i
    then pure (core.result.Result.Err AdapterRw.aspis_r1_cost_probe.verifier.Error.Checkpoint)
    else
      let g ← effects.op17 29#usize p.gamma
      effects.op13 obs AdapterRw.aspis_r1_cost_probe.verifier.Phase.CheckpointRead
      let i1 ← effects.op23
      let i2 ← effects.op22
      let s ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
          { start := i1, «end» := i2 }
      let o ← effects.op2 s
      let r1 ← effects.op0 o AdapterRw.aspis_r1_cost_probe.verifier.Error.Parse
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let i3 ← effects.op15
        let i4 ← effects.op14
        let s1 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
            { start := i3, «end» := i4 }
        let r2 ←
          core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8
            s1
        let folded_root ←
          effects.unwrap32 r2
        let r3 ←
          effects.op5 aspis_coredigestDigest32Inst proof p
            folded_root 1#usize hash
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          effects.op13 obs (AdapterRw.aspis_r1_cost_probe.verifier.Phase.Merkle i)
          let r4 ← effects.op11 p.queries a.next 22#usize
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val2 =>
            let s2 := alloc.vec.Vec.deref a.weights
            let r5 ← effects.op10 s2
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue val3 =>
              let r6 ←
                effects.op6 proof p a g obs val2 val3
                  22#usize
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue val4 =>
                tail effects proof p obs val1 i2 i3 i4 val4
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

theorem common_source {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (pub proof checkpoint : Slice U8) (obs : Option (verifier.Phase → Result Unit)) :
    common traceEffects D pub proof checkpoint hash obs =
      VTop_Flow.tx2_common traceEffects D pub proof checkpoint hash obs := rfl

#print axioms common_source
end AspisR1.VTop_SecondFlow
end

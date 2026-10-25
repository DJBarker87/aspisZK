import VTop_OracleCode
import VTop_Flow
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port8EFF_Control
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
-- Exact suffix of VTop_Flow.tx2_common, only effects dictionary specialized.
def commonTail {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (public_bytes proof : Slice U8) (hash : Hash)
    (obs : Option (verifier.Phase → Result Unit))
    (r : core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) :
    Code (core.result.Result Unit verifier.Error) := do
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (p, a) := val
    let i ← VTop_Flow.traceEffects.op16
    if a.next != i
    then pure (core.result.Result.Err AdapterRw.aspis_r1_cost_probe.verifier.Error.Checkpoint)
    else
      let g ← VTop_Flow.traceEffects.op17 29#usize p.gamma
      VTop_Flow.traceEffects.op13 obs AdapterRw.aspis_r1_cost_probe.verifier.Phase.CheckpointRead
      let i1 ← VTop_Flow.traceEffects.op23
      let i2 ← VTop_Flow.traceEffects.op22
      let s ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
          { start := i1, «end» := i2 }
      let o ← VTop_Flow.traceEffects.op2 s
      let r1 ← VTop_Flow.traceEffects.op0 o AdapterRw.aspis_r1_cost_probe.verifier.Error.Parse
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let i3 ← VTop_Flow.traceEffects.op15
        let i4 ← VTop_Flow.traceEffects.op14
        let s1 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
            { start := i3, «end» := i4 }
        let r2 ←
          core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8
            s1
        let folded_root ←
          VTop_Flow.traceEffects.unwrap32 r2
        let r3 ←
          VTop_Flow.traceEffects.op5 D proof p
            folded_root 1#usize hash
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          VTop_Flow.traceEffects.op13 obs (AdapterRw.aspis_r1_cost_probe.verifier.Phase.Merkle i)
          let r4 ← VTop_Flow.traceEffects.op11 p.queries a.next 22#usize
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val2 =>
            let s2 := alloc.vec.Vec.deref a.weights
            let r5 ← VTop_Flow.traceEffects.op10 s2
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue val3 =>
              let r6 ←
                VTop_Flow.traceEffects.op6 proof p a g obs val2 val3
                  22#usize
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue val4 =>
                let (a1, pending) := val4
                let (s3, deref_mut_back) ←
                  lift (alloc.vec.Vec.deref_mut a1.weights)
                let s4 ← VTop_Flow.traceEffects.op9 pending s3
                let weights := deref_mut_back s4
                let s5 ← lift (Array.to_slice (Std.Array.empty Std.U8))
                let s6 ← lift (Array.to_slice (Std.Array.empty Std.U8))
                let s7 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
                    { start := i2, «end» := i3 }
                let i5 ← VTop_Flow.traceEffects.op21
                let s8 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
                    { start := i4, «end» := i5 }
                let i6 ← VTop_Flow.traceEffects.op20
                let s9 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
                    { start := i5, «end» := i6 }
                let s10 ← lift (Array.to_slice (Std.Array.empty Std.U8))
                VTop_Flow.traceEffects.op19
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
                  } p { a1 with weights } obs
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


def afterPowers {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (proof : Slice U8) (hash : Hash) (obs : Option (verifier.Phase → Result Unit))
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    Code (core.result.Result Unit verifier.Error) := do
  VTop_Flow.traceEffects.op13 obs AdapterRw.aspis_r1_cost_probe.verifier.Phase.CheckpointRead
  let i1 ← VTop_Flow.traceEffects.op23
  let i2 ← VTop_Flow.traceEffects.op22
  let s ←
    core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
      { start := i1, «end» := i2 }
  let o ← VTop_Flow.traceEffects.op2 s
  let r1 ← VTop_Flow.traceEffects.op0 o AdapterRw.aspis_r1_cost_probe.verifier.Error.Parse
  let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf1 with
  | core.ops.control_flow.ControlFlow.Continue val1 =>
    let i3 ← VTop_Flow.traceEffects.op15
    let i4 ← VTop_Flow.traceEffects.op14
    let s1 ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
        { start := i3, «end» := i4 }
    let r2 ←
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8
        s1
    let folded_root ←
      VTop_Flow.traceEffects.unwrap32 r2
    let r3 ←
      VTop_Flow.traceEffects.op5 D proof p
        folded_root 1#usize hash
    let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
    match cf2 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      VTop_Flow.traceEffects.op13 obs (AdapterRw.aspis_r1_cost_probe.verifier.Phase.Merkle i)
      let r4 ← VTop_Flow.traceEffects.op11 p.queries a.next 22#usize
      let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
      match cf3 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let s2 := alloc.vec.Vec.deref a.weights
        let r5 ← VTop_Flow.traceEffects.op10 s2
        let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
        match cf4 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let r6 ←
            VTop_Flow.traceEffects.op6 proof p a g obs val2 val3
              22#usize
          let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
          match cf5 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            let (a1, pending) := val4
            let (s3, deref_mut_back) ←
              lift (alloc.vec.Vec.deref_mut a1.weights)
            let s4 ← VTop_Flow.traceEffects.op9 pending s3
            let weights := deref_mut_back s4
            let s5 ← lift (Array.to_slice (Std.Array.empty Std.U8))
            let s6 ← lift (Array.to_slice (Std.Array.empty Std.U8))
            let s7 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
                { start := i2, «end» := i3 }
            let i5 ← VTop_Flow.traceEffects.op21
            let s8 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
                { start := i4, «end» := i5 }
            let i6 ← VTop_Flow.traceEffects.op20
            let s9 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
                { start := i5, «end» := i6 }
            let s10 ← lift (Array.to_slice (Std.Array.empty Std.U8))
            VTop_Flow.traceEffects.op19
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
              } p { a1 with weights } obs
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

def afterSplit {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (proof : Slice U8) (hash : Hash) (obs : Option (verifier.Phase → Result Unit))
    (p : verifier.Prepared) (a : verifier.Accumulator) (i : Usize) :
    Code (core.result.Result Unit verifier.Error) :=
  if a.next != i then .done (.Err .Checkpoint)
  else .call (.op17 29#usize p.gamma) (afterPowers D proof hash obs p a)

theorem common_ok (impl : Implementation) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (pub proof : Slice U8) (hash : Hash) (p : verifier.Prepared) (a : verifier.Accumulator)
    (H : Bytes → State) :
    eval H (interpret impl (commonTail D pub proof hash none (.Ok (p,a))))=
      eval H (interpret impl (.call .op16 (afterSplit D proof hash none p a))) := rfl

#print axioms common_ok

theorem common_source {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (pub proof ck : Slice U8) (hash : Hash) :
    VTop_Flow.tx2_common VTop_Flow.traceEffects D pub proof ck hash none=
      .call (.op18 D ck proof pub .S2 hash) (commonTail D pub proof hash none) := rfl

theorem rejected (impl : Implementation) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (pub proof : Slice U8) (hash : Hash) (e : verifier.Error) (H : Bytes → State) :
    eval H (interpret impl (commonTail D pub proof hash none (.Err e)))=([],ok (.Err e)) := rfl

#print axioms common_source
#print axioms rejected
end AspisR1.Port8EFF_Control
end

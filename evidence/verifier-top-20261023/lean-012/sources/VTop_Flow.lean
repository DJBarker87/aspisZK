import VTop_Trace
set_option autoImplicit false
noncomputable section
namespace AspisR1.VTop_Flow
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace
universe v
structure Effects (M : Type → Type v) where
  op0 : ∀ {T : Type} {E : Type}, (Option T) → E → M (core.result.Result T E)
  op1 : M aspis_core.field.wide_exact.WideExact
  op2 : (Slice Std.U8) → M (Option aspis_core.field.wide_exact.WideExact)
  op3 : (Slice Std.U8) → M (core.result.Result transport.Variant verifier.Error)
  op4 : (Slice Std.U8) → M (core.result.Result Unit verifier.Error)
  op5 : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H), (Slice Std.U8) → verifier.Prepared → (Array Std.U8 32#usize) → Std.Usize → H → M (core.result.Result Unit verifier.Error)
  op6 : (Slice Std.U8) → verifier.Prepared → verifier.Accumulator → (Array aspis_core.field.wide_exact.WideExact 29#usize) → (Option (verifier.Phase → Result Unit)) → verifier.QueryGeometry → verifier.BatchedWeights → Std.Usize → M (core.result.Result (verifier.Accumulator × verifier.BatchedWeights) verifier.Error)
  op7 : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H), aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → (Slice Std.U8) → H → (Option (verifier.Phase → Result Unit)) → (Array aspis_core.field.wide_exact.WideExact 29#usize) → M ((core.result.Result verifier.Prepared verifier.Error) × (Array aspis_core.field.wide_exact.WideExact 29#usize))
  op8 : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H), verifier.Prepared → verifier.Accumulator → (Slice Std.U8) → (Slice Std.U8) → H → M (alloc.vec.Vec Std.U8)
  op9 : verifier.BatchedWeights → (Slice aspis_core.field.QM31) → M (Slice aspis_core.field.QM31)
  op10 : (Slice aspis_core.field.QM31) → M (core.result.Result verifier.BatchedWeights verifier.Error)
  op11 : (Array Std.U32 22#usize) → Std.Usize → Std.Usize → M (core.result.Result verifier.QueryGeometry verifier.Error)
  op12 : transport.Variant → M (core.result.Result verifier.Accumulator verifier.Error)
  op13 : (Option (verifier.Phase → Result Unit)) → verifier.Phase → M Unit
  op14 : M Std.Usize
  op15 : M Std.Usize
  op16 : M Std.Usize
  op17 : ∀ (N : Std.Usize), aspis_core.field.wide_exact.WideExact → M (Array aspis_core.field.wide_exact.WideExact N)
  op18 : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H), (Slice Std.U8) → (Slice Std.U8) → (Slice Std.U8) → transport.Variant → H → M (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error)
  op19 : verifier.View → verifier.Prepared → verifier.Accumulator → (Option (verifier.Phase → Result Unit)) → M (core.result.Result Unit verifier.Error)
  op20 : M Std.Usize
  op21 : M Std.Usize
  op22 : M Std.Usize
  op23 : M Std.Usize
  unwrap32 : core.result.Result (Array Std.U8 32#usize) core.array.TryFromSliceError → M (Array Std.U8 32#usize)

def sourceEffects (ops : Ops) : Effects Result := {
  op0 := ops.op0
  op1 := ops.op1
  op2 := ops.op2
  op3 := ops.op3
  op4 := ops.op4
  op5 := ops.op5
  op6 := ops.op6
  op7 := ops.op7
  op8 := ops.op8
  op9 := ops.op9
  op10 := ops.op10
  op11 := ops.op11
  op12 := ops.op12
  op13 := ops.op13
  op14 := ops.op14
  op15 := ops.op15
  op16 := ops.op16
  op17 := ops.op17
  op18 := ops.op18
  op19 := ops.op19
  op20 := ops.op20
  op21 := ops.op21
  op22 := ops.op22
  op23 := ops.op23
  unwrap32 := ops.unwrap32
}

def traceEffects : Effects Code := {
  op0 := fun {T} {E} a0 a1 => perform (.op0 (T := T) (E := E) a0 a1)
  op1 := perform (.op1 )
  op2 := fun a0 => perform (.op2 a0)
  op3 := fun a0 => perform (.op3 a0)
  op4 := fun a0 => perform (.op4 a0)
  op5 := fun {H} aspis_coredigestDigest32Inst a0 a1 a2 a3 a4 => perform (.op5 (H := H) aspis_coredigestDigest32Inst a0 a1 a2 a3 a4)
  op6 := fun a0 a1 a2 a3 a4 a5 a6 a7 => perform (.op6 a0 a1 a2 a3 a4 a5 a6 a7)
  op7 := fun {H} aspis_coredigestDigest32Inst a0 a1 a2 a3 a4 => perform (.op7 (H := H) aspis_coredigestDigest32Inst a0 a1 a2 a3 a4)
  op8 := fun {H} aspis_coredigestDigest32Inst a0 a1 a2 a3 a4 => perform (.op8 (H := H) aspis_coredigestDigest32Inst a0 a1 a2 a3 a4)
  op9 := fun a0 a1 => perform (.op9 a0 a1)
  op10 := fun a0 => perform (.op10 a0)
  op11 := fun a0 a1 a2 => perform (.op11 a0 a1 a2)
  op12 := fun a0 => perform (.op12 a0)
  op13 := fun a0 a1 => perform (.op13 a0 a1)
  op14 := perform (.op14 )
  op15 := perform (.op15 )
  op16 := perform (.op16 )
  op17 := fun N a0 => perform (.op17 N a0)
  op18 := fun {H} aspis_coredigestDigest32Inst a0 a1 a2 a3 a4 => perform (.op18 (H := H) aspis_coredigestDigest32Inst a0 a1 a2 a3 a4)
  op19 := fun a0 a1 a2 a3 => perform (.op19 a0 a1 a2 a3)
  op20 := perform (.op20 )
  op21 := perform (.op21 )
  op22 := perform (.op22 )
  op23 := perform (.op23 )
  unwrap32 := fun a0 => perform (.unwrap32 a0)
}

def tx1 {M : Type → Type v} [Monad M] [MonadLiftT Result M] (effects : Effects M)
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (public_bytes : Slice Std.U8) (proof : Slice Std.U8) (k : Std.Usize)
  (hash : H) (obs : Option (verifier.Phase → Result Unit)) :
  M (core.result.Result (alloc.vec.Vec Std.U8) verifier.Error)
  := do
  let i ← effects.op16
  if k != i
  then pure (core.result.Result.Err AdapterRw.aspis_r1_cost_probe.verifier.Error.Parse)
  else
    let r ← effects.op3 proof
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.effects.control_flow.ControlFlow.Continue _ =>
      let r1 ← effects.op4 proof
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.effects.control_flow.ControlFlow.Continue _ =>
        effects.op13 obs AdapterRw.aspis_r1_cost_probe.verifier.Phase.Parsed
        let we ← effects.op1
        let g := Array.repeat 29#usize we
        let (r2, g1) ←
          effects.op7 aspis_coredigestDigest32Inst public1 proof
            hash obs g
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.effects.control_flow.ControlFlow.Continue val =>
          let r3 ← effects.op12 AspisR1Stage2.transport.Variant.S2
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
          match cf3 with
          | core.effects.control_flow.ControlFlow.Continue val1 =>
            effects.op13 obs AdapterRw.aspis_r1_cost_probe.verifier.Phase.Prepare
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
              effects.op5 aspis_coredigestDigest32Inst
                proof val folded_root 0#usize hash
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf4 with
            | core.effects.control_flow.ControlFlow.Continue _ =>
              effects.op13 obs (AdapterRw.aspis_r1_cost_probe.verifier.Phase.Merkle 0#usize)
              let r6 ← effects.op11 val.queries 0#usize k
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
              match cf5 with
              | core.effects.control_flow.ControlFlow.Continue val2 =>
                let s1 := alloc.vec.Vec.deref val1.weights
                let r7 ← effects.op10 s1
                let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r7
                match cf6 with
                | core.effects.control_flow.ControlFlow.Continue val3 =>
                  let r8 ←
                    effects.op6 proof val val1 g1 obs val2
                      val3 k
                  let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r8
                  match cf7 with
                  | core.effects.control_flow.ControlFlow.Continue val4 =>
                    let (a, pending) := val4
                    let (s2, deref_mut_back) ←
                      lift (alloc.vec.Vec.deref_mut a.weights)
                    let s3 ← effects.op9 pending s2
                    let v := deref_mut_back s3
                    let bytes ←
                      effects.op8 aspis_coredigestDigest32Inst val
                        { a with weights := v } proof public_bytes hash
                    effects.op13 obs AdapterRw.aspis_r1_cost_probe.verifier.Phase.CheckpointWrite
                    pure (core.result.Result.Ok bytes)
                  | core.effects.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      (alloc.vec.Vec Std.U8) (core.convert.FromSame
                      verifier.Error) residual
                | core.effects.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    (alloc.vec.Vec Std.U8) (core.convert.FromSame
                    verifier.Error) residual
              | core.effects.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
                  residual
            | core.effects.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
                residual
          | core.effects.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
              residual
        | core.effects.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
            residual
      | core.effects.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
          residual
    | core.effects.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual

def tx2_common {M : Type → Type v} [Monad M] [MonadLiftT Result M] (effects : Effects M)
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
  | core.effects.control_flow.ControlFlow.Continue val =>
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
      | core.effects.control_flow.ControlFlow.Continue val1 =>
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
        | core.effects.control_flow.ControlFlow.Continue _ =>
          effects.op13 obs (AdapterRw.aspis_r1_cost_probe.verifier.Phase.Merkle i)
          let r4 ← effects.op11 p.queries a.next 22#usize
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf3 with
          | core.effects.control_flow.ControlFlow.Continue val2 =>
            let s2 := alloc.vec.Vec.deref a.weights
            let r5 ← effects.op10 s2
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf4 with
            | core.effects.control_flow.ControlFlow.Continue val3 =>
              let r6 ←
                effects.op6 proof p a g obs val2 val3
                  22#usize
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
              match cf5 with
              | core.effects.control_flow.ControlFlow.Continue val4 =>
                let (a1, pending) := val4
                let (s3, deref_mut_back) ←
                  lift (alloc.vec.Vec.deref_mut a1.weights)
                let s4 ← effects.op9 pending s3
                let weights := deref_mut_back s4
                let s5 ← lift (Array.to_slice (Std.Array.empty Std.U8))
                let s6 ← lift (Array.to_slice (Std.Array.empty Std.U8))
                let s7 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
                    { start := i2, «end» := i3 }
                let i5 ← effects.op21
                let s8 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
                    { start := i4, «end» := i5 }
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
                    inactive := val1,
                    round0 := s7,
                    folded_root := none,
                    round1 := s8,
                    final_message := s9,
                    query_bytes := s10
                  } p { a1 with weights } obs
              | core.effects.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  Unit (core.convert.FromSame verifier.Error) residual
            | core.effects.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                Unit (core.convert.FromSame verifier.Error) residual
          | core.effects.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Unit (core.convert.FromSame verifier.Error) residual
        | core.effects.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            Unit (core.convert.FromSame verifier.Error) residual
      | core.effects.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame verifier.Error) residual
  | core.effects.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame verifier.Error) residual

def tx2_authenticated {M : Type → Type v} [Monad M] [MonadLiftT Result M] (effects : Effects M)
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (public_bytes : Slice Std.U8) (proof : Slice Std.U8)
  (checkpoint : Slice Std.U8) (hash : H)
  (obs : Option (verifier.Phase → Result Unit)) :
  M (core.result.Result Unit verifier.Error)
  := do
  let r ← effects.op3 proof
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.effects.control_flow.ControlFlow.Continue _ =>
    effects.op13 obs AdapterRw.aspis_r1_cost_probe.verifier.Phase.Parsed
    (tx2_common effects) aspis_coredigestDigest32Inst public_bytes
      proof checkpoint hash obs
  | core.effects.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame verifier.Error) residual

end AspisR1.VTop_Flow
end

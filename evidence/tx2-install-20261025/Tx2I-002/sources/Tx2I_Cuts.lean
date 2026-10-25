import Tx2I_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.Tx2I_Cuts
open Aeneas Aeneas.Std Result VTop_Stages
def tail (ops : VTop_Stages.Ops)
    (proof : Slice U8) (p : verifier.Prepared) (obs : Option (verifier.Phase → Result Unit))
    (inactive : aspis_core.field.wide_exact.WideExact) (round0 folded round1 : Usize)
    (state : verifier.Accumulator × verifier.BatchedWeights) : Result (core.result.Result Unit verifier.Error) := do
  let (a1, pending) := state
  let (s3, deref_mut_back) ←
    lift (alloc.vec.Vec.deref_mut a1.weights)
  let s4 ← ops.op9 pending s3
  let weights := deref_mut_back s4
  let s5 ← lift (Array.to_slice (Std.Array.empty Std.U8))
  let s6 ← lift (Array.to_slice (Std.Array.empty Std.U8))
  let s7 ←
    core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
      { start := round0, «end» := folded }
  let i5 ← ops.op21
  let s8 ←
    core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
      { start := round1, «end» := i5 }
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
      inactive := inactive,
      round0 := s7,
      folded_root := none,
      round1 := s8,
      final_message := s9,
      query_bytes := s10
    } p { a1 with weights } obs

def common (ops : VTop_Stages.Ops)
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (public_bytes : Slice Std.U8) (proof : Slice Std.U8)
  (checkpoint : Slice Std.U8) (hash : H)
  (obs : Option (verifier.Phase → Result Unit)) :
  Result (core.result.Result Unit verifier.Error)
  := do
  let r ←
    ops.op18 aspis_coredigestDigest32Inst checkpoint proof public_bytes
      AspisR1Stage2.transport.Variant.S2 hash
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (p, a) := val
    let i ← ops.op16
    if a.next != i
    then ok (core.result.Result.Err AdapterRw.aspis_r1_cost_probe.verifier.Error.Checkpoint)
    else
      let g ← ops.op17 29#usize p.gamma
      ops.op13 obs AdapterRw.aspis_r1_cost_probe.verifier.Phase.CheckpointRead
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
          ops.op5 aspis_coredigestDigest32Inst proof p
            folded_root 1#usize hash
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          ops.op13 obs (AdapterRw.aspis_r1_cost_probe.verifier.Phase.Merkle i)
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
                ops.op6 proof p a g obs val2 val3
                  22#usize
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue val4 =>
                tail ops proof p obs val1 i2 i3 i4 val4
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


theorem common_source (ops : VTop_Stages.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8) (obs : Option (verifier.Phase → Result Unit)) :
    common ops D pub proof checkpoint hash obs =
      verifier.candidate.tx2_common ops D pub proof checkpoint hash obs := rfl

theorem tail_reached (ops : VTop_Stages.Ops) (proof : Slice U8) (p : verifier.Prepared)
    (obs : Option (verifier.Phase → Result Unit))
    (inactive : aspis_core.field.wide_exact.WideExact) (round0 folded round1 : Usize)
    (state : verifier.Accumulator × verifier.BatchedWeights)
    (accepted : tail ops proof p obs inactive round0 folded round1 state = ok (.Ok ())) :
    ∃ (flushed : Slice aspis_core.field.QM31)
      (back : Slice aspis_core.field.QM31 → alloc.vec.Vec aspis_core.field.QM31)
      (v : verifier.View),
      alloc.vec.Vec.deref_mut state.1.weights = (state.1.weights.deref,back) ∧
      ops.op9 state.2 state.1.weights.deref = ok flushed ∧
      ops.op19 v p {state.1 with weights := back flushed} obs = ok (.Ok ()) := by
  unfold tail at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals exact ⟨_,_,_,rfl,by assumption,accepted⟩

attribute [local irreducible] tail

theorem common_reached (ops : VTop_Stages.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8) (obs : Option (verifier.Phase → Result Unit))
    (accepted : verifier.candidate.tx2_common ops D pub proof checkpoint hash obs = ok (.Ok ())) :
    ∃ (p : verifier.Prepared) (saved : verifier.Accumulator)
      (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
      (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
      (returned : verifier.Accumulator) (after : verifier.BatchedWeights)
      (flushed : Slice aspis_core.field.QM31)
      (back : Slice aspis_core.field.QM31 → alloc.vec.Vec aspis_core.field.QM31)
      (v : verifier.View),
      ops.op18 D checkpoint proof pub .S2 hash = ok (.Ok (p,saved)) ∧
      ops.op6 proof p saved g obs geometry pending 22#usize = ok (.Ok (returned,after)) ∧
      alloc.vec.Vec.deref_mut returned.weights = (returned.weights.deref,back) ∧
      ops.op9 after returned.weights.deref = ok flushed ∧
      ops.op19 v p {returned with weights := back flushed} obs = ok (.Ok ()) := by
  rw [← common_source ops D hash pub proof checkpoint obs] at accepted
  unfold common at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals
    obtain ⟨flushed,back,v,hd,hf,hfinish⟩ := tail_reached ops proof _ obs _ _ _ _ _ accepted
    exact ⟨_,_,_,_,_,_,_,flushed,back,v,by assumption,by assumption,hd,hf,hfinish⟩

theorem authenticated_reached (ops : VTop_Stages.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8) (obs : Option (verifier.Phase → Result Unit))
    (accepted : verifier.candidate.tx2_authenticated ops D pub proof checkpoint hash obs = ok (.Ok ())) :
    ∃ variant, ops.op3 proof = ok (.Ok variant) ∧
      verifier.candidate.tx2_common ops D pub proof checkpoint hash obs = ok (.Ok ()) := by
  unfold verifier.candidate.tx2_authenticated at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals exact ⟨_,by assumption,accepted⟩

#print axioms common_source
#print axioms tail_reached
#print axioms common_reached
#print axioms authenticated_reached
end AspisR1.Tx2I_Cuts
end

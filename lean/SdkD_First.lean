import SdkD_Control
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_First
open Aeneas Aeneas.Std Result AspisR1CurrentCaller SdkD_Control
def code (ops : Ops)
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (public_bytes : Slice Std.U8) (proof : Slice Std.U8) (k : Std.Usize)
  (hash : H) (obs : Option (verifier.Phase → Result Unit)) :
  Code (core.result.Result (alloc.vec.Vec Std.U8) verifier.Error)
  := do
  if k != compact.SPLIT
  then pure (core.result.Result.Err verifier.Error.Parse)
  else
    let r ← ops.op3 proof
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let r1 ← ops.op4 proof
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        verifier.mark obs verifier.Phase.Parsed
        let we ← (aspis_core.field.wide_exact.WideExact.ZERO ops)
        let g := Array.repeat 29#usize we
        let (r2, g1) ←
          (verifier.candidate.prepare ops) aspis_coredigestDigest32Inst public1 proof
            hash obs g
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val =>
          let r3 ← ops.op20 transport.Variant.S2
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val1 =>
            verifier.mark obs verifier.Phase.Prepare
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
              emit .batch0 (ops.op6 aspis_coredigestDigest32Inst
                proof val folded_root 0#usize hash)
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              verifier.mark obs (verifier.Phase.Merkle 0#usize)
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
                    emit .query0 (ops.op7 proof val val1 g1 obs val2
                      val3 k)
                  let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r8
                  match cf7 with
                  | core.ops.control_flow.ControlFlow.Continue val4 =>
                    let (a, pending) := val4
                    let (s2, deref_mut_back) ←
                      lift (alloc.vec.Vec.deref_mut a.weights)
                    let s3 ← ops.op17 pending s2
                    let v := deref_mut_back s3
                    let bytes ←
                      emit .save (ops.op16 aspis_coredigestDigest32Inst val
                        { a with weights := v } proof public_bytes hash)
                    verifier.mark obs verifier.Phase.CheckpointWrite
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

theorem erase_pure {A : Type} (a : A) : erase (pure a : Code A) = ok a := rfl

theorem erase_liftM {A : Type} (r : Result A) : erase (monadLift r : Code A) = r := erase_lift r

private theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a, f a = g a) : (r >>= f) = (r >>= g) :=
  congrArg (fun k => r >>= k) (funext h)

theorem source (ops : Ops) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (obs : Option (verifier.Phase → Result Unit)) :
    erase (code ops D semantic pub proof split hash obs) =
      verifier.candidate.tx1 ops D semantic pub proof split hash obs := by
  simp only [code,verifier.candidate.tx1,erase_bind,erase_liftM,erase_pure,erase_emit]
  all_goals repeat' first
    | (with_reducible rfl)
    | (fail_if_no_progress simp only [erase_bind,erase_liftM,erase_pure,erase_emit,erase,liftResult])
    | (apply bind_congr; intro x)
    | split

#print axioms erase_pure
#print axioms erase_liftM
#print axioms bind_congr
#print axioms source
end AspisR1.SdkD_First
end

import NCT_DriverDomain
import NBA_QueryJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCU_WriterPrefix
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
/-- The emitted release driver up to its writer invocation. No writer success
is required. `factor` below checks this factor against the original body for
ALL outer/inner outcomes, not just accepted runs. -/
def beforeWriter (ops : Ops)
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (public_bytes : Slice Std.U8) (proof : Slice Std.U8) (k : Std.Usize)
  (hash : H)  :
  Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error)
  := do
  if k != compact.SPLIT
  then ok (core.result.Result.Err verifier.Error.Parse)
  else
    let r ← ops.op3 proof
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let r1 ← ops.op4 proof
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        verifier.mark none verifier.Phase.Parsed
        let we ← (aspis_core.field.wide_exact.WideExact.ZERO ops)
        let g := Array.repeat 29#usize we
        let (r2, g1) ←
          (verifier.candidate.prepare ops) aspis_coredigestDigest32Inst public1 proof
            hash none g
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val =>
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
        (verifier.Prepared × verifier.Accumulator) (core.convert.FromSame verifier.Error) residual

def finish (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub proof : Slice U8) (hash : H)
    (prefix : Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error)) :
    Result (core.result.Result (alloc.vec.Vec U8) verifier.Error) := do
  let r ← prefix
  match r with
  | .Err error => ok (.Err error)
  | .Ok (p,a) => do
    let bytes ← ops.op16 D p a proof pub hash
    ok (.Ok bytes)

theorem factor (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (hash : H) :
    verifier.candidate.tx1 ops D semantic pub proof split hash none =
      finish ops D pub proof hash (beforeWriter ops D semantic pub proof split hash) := by
  unfold verifier.candidate.tx1 beforeWriter finish
  simp only [bind_assoc_eq]
  split
  · rfl
  · apply NBA_QueryJoin.bind_same
    intro parsed
    cases parsed <;> simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from]
    · rfl
    · repeat' first
      | rfl
      | (apply NBA_QueryJoin.bind_same; intro x)
      | (split <;> simp only [bind_tc_ok,bind_assoc_eq])

#print axioms factor
end AspisR1.NCU_WriterPrefix
end

import NBN_AfterDecodeTypes
import NBN_AfterDecode04
set_option autoImplicit false
noncomputable section
namespace NBN_AfterDecode00
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1TerminalDecoder pool_v1.pair_terminal NBN_AfterDecodeTypes

def run (decode : Decode) (bytes : Slice U8) (val1 : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairVerifiedAfterstateV1 PoolV1PairVerifierTransportErrorV1) := do
  let s3 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 48#usize, «end» := 80#usize }
  let r3 ← pool_v1.pair_terminal.exact 32#usize s3
  let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
  match cf2 with
  | core.ops.control_flow.ControlFlow.Continue val2 =>
    let r4 ← decode val2
    let r5 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r4 ()
    let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r5
    match cf3 with
    | core.ops.control_flow.ControlFlow.Continue val3 =>
      let s4 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 80#usize, «end» := 112#usize }
      let r6 ← pool_v1.pair_terminal.exact 32#usize s4
      let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r6
      match cf4 with
      | core.ops.control_flow.ControlFlow.Continue val4 =>
        let r7 ← decode val4
        let r8 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r7 ()
        let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r8
        match cf5 with
        | core.ops.control_flow.ControlFlow.Continue val5 =>
          let s5 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 112#usize, «end» := 144#usize }
          let r9 ← pool_v1.pair_terminal.exact 32#usize s5
          let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r9
          match cf6 with
          | core.ops.control_flow.ControlFlow.Continue val6 =>
            let r10 ← decode val6
            let r11 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r10 ()
            let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r11
            match cf7 with
            | core.ops.control_flow.ControlFlow.Continue val7 =>
              let s6 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 144#usize, «end» := 176#usize }
              let r12 ← pool_v1.pair_terminal.exact 32#usize s6
              let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r12
              match cf8 with
              | core.ops.control_flow.ControlFlow.Continue val8 =>
                let r13 ← decode val8
                let r14 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r13 ()
                let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r14
                match cf9 with
                | core.ops.control_flow.ControlFlow.Continue val9 =>
                  NBN_AfterDecode04.run decode bytes val1 val3 val5 val7 val9
                | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
              | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
            | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
          | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual

theorem source (decode : Decode) (lower : NBN_Dep_DigestDecode decode)
    (bytes : Slice U8) (val1 : Array aspis_core.field.M31 8#usize) :
    run decode bytes val1 = AspisS6NativeAfterstateDecoderFactored.part_0 bytes val1 := by
  have same : decode = atomic_statement.decode_digest_canonical := funext lower
  unfold run
  simp only [NBN_AfterDecode04.source decode lower]
  rw [same]
  unfold AspisS6NativeAfterstateDecoderFactored.part_0
  run_tac do
    for _ in [:8] do
      let g ← Lean.Elab.Tactic.getMainGoal
      let t ← g.getType
      let names := t.getUsedConstants.filter fun n =>
        let s := n.toString
        (s.startsWith "NBN_AfterDecode" || s.startsWith "AspisS6NativeAfterstateDecoderFactored.") &&
        (s.splitOn ".").any (fun c => c.startsWith "match_")
      if names.isEmpty then break
      let ids := names.map Lean.mkIdent
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $[$ids:ident]*))
  dsimp only
  all_goals with_reducible rfl

#print axioms source
end NBN_AfterDecode00

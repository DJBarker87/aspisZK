import NBN_AfterDecodeTypes
import NBN_AfterDecode12
set_option autoImplicit false
noncomputable section
namespace NBN_AfterDecode08
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1TerminalDecoder pool_v1.pair_terminal NBN_AfterDecodeTypes

def run (decode : Decode) (bytes : Slice U8) (val1 val3 val5 val7 val9 val11 val13 val15 val17 : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairVerifiedAfterstateV1 PoolV1PairVerifierTransportErrorV1) := do
  let s11 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 304#usize, «end» := 336#usize }
  let r27 ← pool_v1.pair_terminal.exact 32#usize s11
  let cf18 ← core.result.Result.Insts.CoreOpsTry.branch r27
  match cf18 with
  | core.ops.control_flow.ControlFlow.Continue val18 =>
    let r28 ← decode val18
    let r29 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_9.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r28 ()
    let cf19 ← core.result.Result.Insts.CoreOpsTry.branch r29
    match cf19 with
    | core.ops.control_flow.ControlFlow.Continue val19 =>
      let s12 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 336#usize, «end» := 368#usize }
      let r30 ← pool_v1.pair_terminal.exact 32#usize s12
      let cf20 ← core.result.Result.Insts.CoreOpsTry.branch r30
      match cf20 with
      | core.ops.control_flow.ControlFlow.Continue val20 =>
        let r31 ← decode val20
        let r32 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_10.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r31 ()
        let cf21 ← core.result.Result.Insts.CoreOpsTry.branch r32
        match cf21 with
        | core.ops.control_flow.ControlFlow.Continue val21 =>
          let s13 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 368#usize, «end» := 400#usize }
          let r33 ← pool_v1.pair_terminal.exact 32#usize s13
          let cf22 ← core.result.Result.Insts.CoreOpsTry.branch r33
          match cf22 with
          | core.ops.control_flow.ControlFlow.Continue val22 =>
            let r34 ← decode val22
            let r35 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_11.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r34 ()
            let cf23 ← core.result.Result.Insts.CoreOpsTry.branch r35
            match cf23 with
            | core.ops.control_flow.ControlFlow.Continue val23 =>
              let s14 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 400#usize, «end» := 432#usize }
              let r36 ← pool_v1.pair_terminal.exact 32#usize s14
              let cf24 ← core.result.Result.Insts.CoreOpsTry.branch r36
              match cf24 with
              | core.ops.control_flow.ControlFlow.Continue val24 =>
                let r37 ← decode val24
                let r38 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_12.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r37 ()
                let cf25 ← core.result.Result.Insts.CoreOpsTry.branch r38
                match cf25 with
                | core.ops.control_flow.ControlFlow.Continue val25 =>
                  NBN_AfterDecode12.run decode bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25
                | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
              | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
            | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
          | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual

theorem source (decode : Decode) (lower : NBN_Dep_DigestDecode decode)
    (bytes : Slice U8) (val1 val3 val5 val7 val9 val11 val13 val15 val17 : Array aspis_core.field.M31 8#usize) :
    run decode bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 = AspisS6NativeAfterstateDecoderFactored.part_8 bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 := by
  have same : decode = atomic_statement.decode_digest_canonical := funext lower
  unfold run
  simp only [NBN_AfterDecode12.source decode lower]
  rw [same]
  unfold AspisS6NativeAfterstateDecoderFactored.part_8
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
end NBN_AfterDecode08

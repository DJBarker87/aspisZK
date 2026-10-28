import NBN_AfterDecodeTypes
import NBN_AfterDecode08
set_option autoImplicit false
noncomputable section
namespace NBN_AfterDecode04
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1TerminalDecoder pool_v1.pair_terminal NBN_AfterDecodeTypes

def run (decode : Decode) (bytes : Slice U8) (val1 val3 val5 val7 val9 : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairVerifiedAfterstateV1 PoolV1PairVerifierTransportErrorV1) := do
  let s7 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 176#usize, «end» := 208#usize }
  let r15 ← pool_v1.pair_terminal.exact 32#usize s7
  let cf10 ← core.result.Result.Insts.CoreOpsTry.branch r15
  match cf10 with
  | core.ops.control_flow.ControlFlow.Continue val10 =>
    let r16 ← decode val10
    let r17 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_5.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r16 ()
    let cf11 ← core.result.Result.Insts.CoreOpsTry.branch r17
    match cf11 with
    | core.ops.control_flow.ControlFlow.Continue val11 =>
      let s8 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 208#usize, «end» := 240#usize }
      let r18 ← pool_v1.pair_terminal.exact 32#usize s8
      let cf12 ← core.result.Result.Insts.CoreOpsTry.branch r18
      match cf12 with
      | core.ops.control_flow.ControlFlow.Continue val12 =>
        let r19 ← decode val12
        let r20 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_6.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r19 ()
        let cf13 ← core.result.Result.Insts.CoreOpsTry.branch r20
        match cf13 with
        | core.ops.control_flow.ControlFlow.Continue val13 =>
          let s9 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 240#usize, «end» := 272#usize }
          let r21 ← pool_v1.pair_terminal.exact 32#usize s9
          let cf14 ← core.result.Result.Insts.CoreOpsTry.branch r21
          match cf14 with
          | core.ops.control_flow.ControlFlow.Continue val14 =>
            let r22 ← decode val14
            let r23 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_7.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r22 ()
            let cf15 ← core.result.Result.Insts.CoreOpsTry.branch r23
            match cf15 with
            | core.ops.control_flow.ControlFlow.Continue val15 =>
              let s10 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 272#usize, «end» := 304#usize }
              let r24 ← pool_v1.pair_terminal.exact 32#usize s10
              let cf16 ← core.result.Result.Insts.CoreOpsTry.branch r24
              match cf16 with
              | core.ops.control_flow.ControlFlow.Continue val16 =>
                let r25 ← decode val16
                let r26 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_8.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r25 ()
                let cf17 ← core.result.Result.Insts.CoreOpsTry.branch r26
                match cf17 with
                | core.ops.control_flow.ControlFlow.Continue val17 =>
                  NBN_AfterDecode08.run decode bytes val1 val3 val5 val7 val9 val11 val13 val15 val17
                | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
              | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
            | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
          | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual

theorem source (decode : Decode) (lower : NBN_Dep_DigestDecode decode)
    (bytes : Slice U8) (val1 val3 val5 val7 val9 : Array aspis_core.field.M31 8#usize) :
    run decode bytes val1 val3 val5 val7 val9 = AspisS6NativeAfterstateDecoderFactored.part_4 bytes val1 val3 val5 val7 val9 := by
  have same : decode = atomic_statement.decode_digest_canonical := funext lower
  unfold run
  simp only [NBN_AfterDecode08.source decode lower]
  rw [same]
  unfold AspisS6NativeAfterstateDecoderFactored.part_4
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
end NBN_AfterDecode04

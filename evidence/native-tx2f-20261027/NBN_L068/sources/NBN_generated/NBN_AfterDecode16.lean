import NBN_AfterDecodeTypes
set_option autoImplicit false
noncomputable section
namespace NBN_AfterDecode16
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1TerminalDecoder pool_v1.pair_terminal NBN_AfterDecodeTypes

def run (decode : Decode) (bytes : Slice U8) (val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 val27 val29 val31 val33 : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairVerifiedAfterstateV1 PoolV1PairVerifierTransportErrorV1) := do
  let s19 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 560#usize, «end» := 592#usize }
  let r51 ← pool_v1.pair_terminal.exact 32#usize s19
  let cf34 ← core.result.Result.Insts.CoreOpsTry.branch r51
  match cf34 with
  | core.ops.control_flow.ControlFlow.Continue val34 =>
    let r52 ← decode val34
    let r53 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_17.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r52 ()
    let cf35 ← core.result.Result.Insts.CoreOpsTry.branch r53
    match cf35 with
    | core.ops.control_flow.ControlFlow.Continue val35 =>
      let s20 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 592#usize, «end» := 624#usize }
      let r54 ← pool_v1.pair_terminal.exact 32#usize s20
      let cf36 ← core.result.Result.Insts.CoreOpsTry.branch r54
      match cf36 with
      | core.ops.control_flow.ControlFlow.Continue val36 =>
        let r55 ← decode val36
        let r56 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_18.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r55 ()
        let cf37 ← core.result.Result.Insts.CoreOpsTry.branch r56
        match cf37 with
        | core.ops.control_flow.ControlFlow.Continue val37 =>
          let s21 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 624#usize, «end» := 656#usize }
          let r57 ← pool_v1.pair_terminal.exact 32#usize s21
          let cf38 ← core.result.Result.Insts.CoreOpsTry.branch r57
          match cf38 with
          | core.ops.control_flow.ControlFlow.Continue val38 =>
            let r58 ← decode val38
            let r59 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_19.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r58 ()
            let cf39 ← core.result.Result.Insts.CoreOpsTry.branch r59
            match cf39 with
            | core.ops.control_flow.ControlFlow.Continue val39 =>
              let s22 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 656#usize, «end» := 688#usize }
              let r60 ← pool_v1.pair_terminal.exact 32#usize s22
              let cf40 ← core.result.Result.Insts.CoreOpsTry.branch r60
              match cf40 with
              | core.ops.control_flow.ControlFlow.Continue val40 =>
                let r61 ← decode val40
                let r62 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_20.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r61 ()
                let cf41 ← core.result.Result.Insts.CoreOpsTry.branch r62
                match cf41 with
                | core.ops.control_flow.ControlFlow.Continue val41 =>
                  let s23 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 8#usize, «end» := 16#usize }
                  let r63 ← pool_v1.pair_terminal.exact 8#usize s23
                  let cf42 ← core.result.Result.Insts.CoreOpsTry.branch r63
                  match cf42 with
                  | core.ops.control_flow.ControlFlow.Continue val42 =>
                    let i6 ← lift (core.num.U64.from_le_bytes val42)
                    let r64 ← pool_v1.pair_terminal.validate_verified_afterstate { next_pair_index := i6, next_root := val1, next_frontier := (Array.make 20#usize [ val3, val5, val7, val9, val11, val13, val15, val17, val19, val21, val23, val25, val27, val29, val31, val33, val35, val37, val39, val41 ]) }
                    let cf43 ← core.result.Result.Insts.CoreOpsTry.branch r64
                    match cf43 with
                    | core.ops.control_flow.ControlFlow.Continue _ => ok (core.result.Result.Ok { next_pair_index := i6, next_root := val1, next_frontier := (Array.make 20#usize [ val3, val5, val7, val9, val11, val13, val15, val17, val19, val21, val23, val25, val27, val29, val31, val33, val35, val37, val39, val41 ]) })
                    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
                  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
                | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
              | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
            | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
          | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual

theorem source (decode : Decode) (lower : NBN_Dep_DigestDecode decode)
    (bytes : Slice U8) (val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 val27 val29 val31 val33 : Array aspis_core.field.M31 8#usize) :
    run decode bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 val27 val29 val31 val33 = AspisS6NativeAfterstateDecoderFactored.part_16 bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 val27 val29 val31 val33 := by
  have same : decode = atomic_statement.decode_digest_canonical := funext lower
  unfold run
  rw [same]
  unfold AspisS6NativeAfterstateDecoderFactored.part_16
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
end NBN_AfterDecode16

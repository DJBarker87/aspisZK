import NBN_AfterDecodeTypes
import NBN_AfterDecode16
set_option autoImplicit false
noncomputable section
namespace NBN_AfterDecode12
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1TerminalDecoder pool_v1.pair_terminal NBN_AfterDecodeTypes

def run (decode : Decode) (bytes : Slice U8) (val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairVerifiedAfterstateV1 PoolV1PairVerifierTransportErrorV1) := do
  let s15 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 432#usize, «end» := 464#usize }
  let r39 ← pool_v1.pair_terminal.exact 32#usize s15
  let cf26 ← core.result.Result.Insts.CoreOpsTry.branch r39
  match cf26 with
  | core.ops.control_flow.ControlFlow.Continue val26 =>
    let r40 ← decode val26
    let r41 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_13.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r40 ()
    let cf27 ← core.result.Result.Insts.CoreOpsTry.branch r41
    match cf27 with
    | core.ops.control_flow.ControlFlow.Continue val27 =>
      let s16 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 464#usize, «end» := 496#usize }
      let r42 ← pool_v1.pair_terminal.exact 32#usize s16
      let cf28 ← core.result.Result.Insts.CoreOpsTry.branch r42
      match cf28 with
      | core.ops.control_flow.ControlFlow.Continue val28 =>
        let r43 ← decode val28
        let r44 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_14.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r43 ()
        let cf29 ← core.result.Result.Insts.CoreOpsTry.branch r44
        match cf29 with
        | core.ops.control_flow.ControlFlow.Continue val29 =>
          let s17 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 496#usize, «end» := 528#usize }
          let r45 ← pool_v1.pair_terminal.exact 32#usize s17
          let cf30 ← core.result.Result.Insts.CoreOpsTry.branch r45
          match cf30 with
          | core.ops.control_flow.ControlFlow.Continue val30 =>
            let r46 ← decode val30
            let r47 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_15.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r46 ()
            let cf31 ← core.result.Result.Insts.CoreOpsTry.branch r47
            match cf31 with
            | core.ops.control_flow.ControlFlow.Continue val31 =>
              let s18 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 528#usize, «end» := 560#usize }
              let r48 ← pool_v1.pair_terminal.exact 32#usize s18
              let cf32 ← core.result.Result.Insts.CoreOpsTry.branch r48
              match cf32 with
              | core.ops.control_flow.ControlFlow.Continue val32 =>
                let r49 ← decode val32
                let r50 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_16.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r49 ()
                let cf33 ← core.result.Result.Insts.CoreOpsTry.branch r50
                match cf33 with
                | core.ops.control_flow.ControlFlow.Continue val33 =>
                  NBN_AfterDecode16.run decode bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 val27 val29 val31 val33
                | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
              | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
            | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
          | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual

theorem source (decode : Decode) (lower : NBN_Dep_DigestDecode decode)
    (bytes : Slice U8) (val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 : Array aspis_core.field.M31 8#usize) :
    run decode bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 = AspisS6NativeAfterstateDecoderFactored.part_12 bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 := by
  have same : decode = atomic_statement.decode_digest_canonical := funext lower
  unfold run
  simp only [NBN_AfterDecode16.source decode lower]
  rw [same]
  unfold AspisS6NativeAfterstateDecoderFactored.part_12
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
end NBN_AfterDecode12

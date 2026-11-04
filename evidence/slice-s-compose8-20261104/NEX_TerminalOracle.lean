import AspisR1TerminalDecoder.Funs
set_option autoImplicit false
noncomputable section
namespace NEX_TerminalOracle
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
def run (common : Slice U8 → Result (core.result.Result pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)) (transfer : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 → Slice U8 → Result (core.result.Result pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)) (withdrawal : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 → Slice U8 → Result (core.result.Result pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)) (validate : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 → Result (core.result.Result Unit pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)) (bytes : Slice Std.U8) : Result (core.result.Result pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) := do
  let i := Slice.len bytes
  let i1 ← pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES
  if i != i1
  then ok (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongLength)
  else
    let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bytes { «end» := 4#usize }
    let s1 ← core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC { start := 0#usize, «end» := 4#usize }
    let b ← core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s s1
    if b
    then ok (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongMagic)
    else
      let i2 ← Slice.index_usize bytes 4#usize
      if i2 != pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_VERSION
      then ok (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongVersion)
      else
        let i3 ← Slice.index_usize bytes 5#usize
        let r ← pool_v1.pair_forest_terminal.transition_kind i3
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val =>
          let i4 ← Slice.index_usize bytes 6#usize
          if i4 != pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
          then ok (core.result.Result.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongDigestEncoding)
          else
            let r1 ← common bytes
            let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
            match cf1 with
            | core.ops.control_flow.ControlFlow.Continue val1 =>
              match val with
              | pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer =>
                let i5 ← pool_v1.pair_forest_terminal.PAYMENT_STATEMENT_OFFSET
                let s2 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) bytes { start := i5 }
                let r2 ← transfer val1 s2
                let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
                match cf2 with
                | core.ops.control_flow.ControlFlow.Continue val2 => let r3 ← validate val2
                                                                     let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
                                                                     match cf3 with
                                                                     | core.ops.control_flow.ControlFlow.Continue _ => ok (core.result.Result.Ok val2)
                                                                     | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual
                | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual
              | pool_v1.historical_anchor.PoolV1TransitionKind.Withdrawal =>
                let i5 ← pool_v1.pair_forest_terminal.PAYMENT_STATEMENT_OFFSET
                let s2 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) bytes { start := i5 }
                let r2 ← withdrawal val1 s2
                let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
                match cf2 with
                | core.ops.control_flow.ControlFlow.Continue val2 => let r3 ← validate val2
                                                                     let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
                                                                     match cf3 with
                                                                     | core.ops.control_flow.ControlFlow.Continue _ => ok (core.result.Result.Ok val2)
                                                                     | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual
                | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual
            | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual

/-- Model continuation substitution only. Native certificates and reached
child domains are separate checked obligations; no native root is assumed. -/
theorem result_state_effects {State : Type} (bytes : Slice U8) (state : State) :
    (run pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1 pool_v1.pair_forest_terminal.decode_transfer_statement_boxed_v1 pool_v1.pair_forest_terminal.decode_withdrawal_statement_boxed_v1 pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 bytes,state,([] : List Unit)) =
    (pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 bytes,state,[]) := by rfl
#print axioms result_state_effects
end NEX_TerminalOracle

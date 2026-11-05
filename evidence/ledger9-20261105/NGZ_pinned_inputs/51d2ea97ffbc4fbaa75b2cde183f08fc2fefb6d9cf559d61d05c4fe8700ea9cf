import Lean
import AspisR1TerminalDecoder.Funs

set_option autoImplicit false
noncomputable section
namespace NGF_NEX_CommonOracle
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
def run (digest : Array U8 32#usize → Result (core.result.Result (Array aspis_core.field.M31 8#usize) atomic_statement.AtomicStatementError)) (lane : Slice U8 → Result (core.result.Result pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)) (bytes : Slice Std.U8) : Result (core.result.Result pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) := do
  let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := pool_v1.pair_forest_terminal.HISTORICAL_ANCHOR_OFFSET, «end» := pool_v1.pair_forest_terminal.LATE_STATEMENT_OFFSET }
  let r ← core.array.TryFromSharedArraySlice.try_from 32#usize s
  let r1 ← AspisR1TerminalDecoder.core.result.Result.map_err pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1 r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r2 ← digest val
    let r3 ← AspisR1TerminalDecoder.core.result.Result.map_err pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairForestTerminalFormatErrorV1 r2 ()
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r3
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let i ← pool_v1.pair_forest_terminal.PAYMENT_STATEMENT_OFFSET
      let s1 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := pool_v1.pair_forest_terminal.LATE_STATEMENT_OFFSET, «end» := i }
      let r4 ← lane s1
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r4
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let s2 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := pool_v1.pair_forest_terminal.MASTER_OFFSET, «end» := pool_v1.pair_forest_terminal.CHECKPOINT_ACCOUNT_OFFSET }
        let r5 ← core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s2
        let r6 ← AspisR1TerminalDecoder.core.result.Result.map_err pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1 r5 ()
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r6
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let s3 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := pool_v1.pair_forest_terminal.CHECKPOINT_ACCOUNT_OFFSET, «end» := pool_v1.pair_forest_terminal.SELECTED_LANE_ACCOUNT_OFFSET }
          let r7 ← core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s3
          let r8 ← AspisR1TerminalDecoder.core.result.Result.map_err pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1 r7 ()
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r8
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            let s4 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := pool_v1.pair_forest_terminal.SELECTED_LANE_ACCOUNT_OFFSET, «end» := pool_v1.pair_forest_terminal.CHECKPOINT_SEQUENCE_OFFSET }
            let r9 ← core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s4
            let r10 ← AspisR1TerminalDecoder.core.result.Result.map_err pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1 r9 ()
            let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r10
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue val5 =>
              let i1 ← Slice.index_usize bytes 7#usize
              let s5 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := pool_v1.pair_forest_terminal.CHECKPOINT_SEQUENCE_OFFSET, «end» := pool_v1.pair_forest_terminal.HISTORICAL_ANCHOR_OFFSET }
              let r11 ← core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8 s5
              let r12 ← AspisR1TerminalDecoder.core.result.Result.map_err pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1.closure_5.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1 r11 ()
              let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r12
              match cf6 with
              | core.ops.control_flow.ControlFlow.Continue val6 => let i2 ← lift (core.num.U64.from_le_bytes val6)
                                                                   ok (core.result.Result.Ok { master_account := val3, checkpoint_account := val4, selected_lane_account := val5, output_lane := i1, checkpoint_sequence := i2, historical_global_anchor := val1, lane_transition := val2 })
              | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual
            | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual
          | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual

/-- Model continuation substitution only. Native certificates and reached
child domains are separate checked obligations; no native root is assumed. -/
theorem result_state_effects {State : Type} (bytes : Slice U8) (state : State) :
    (run atomic_statement.decode_digest_canonical pool_v1.pair_forest_terminal.decode_lane_transition_boxed_v1 bytes,state,([] : List Unit)) =
    (pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1 bytes,state,[]) := by rfl
#print axioms result_state_effects
end NGF_NEX_CommonOracle

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))

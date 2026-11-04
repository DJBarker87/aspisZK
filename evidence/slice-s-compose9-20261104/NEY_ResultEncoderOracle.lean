import JHb_S2K_ResultWholeNative
set_option autoImplicit false
noncomputable section
namespace NEY_ResultEncoderOracle
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1TerminalDecoder
abbrev Record := pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1
abbrev Error := pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
abbrev After := pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
abbrev AfterError := pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
def run
  (validate : Record → Result (core.result.Result Unit Error))
  (digest : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize → Result (Array U8 32#usize))
  (after : After → Result (core.result.Result (Array U8 688#usize) AfterError))
  (result : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1) :
  Result (core.result.Result (Array Std.U8 792#usize)
    pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  := do
  let r ← validate result
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let output := Array.repeat 792#usize 0#u8
    let (s, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) output
        { «end» := 4#usize }
    let s1 ←
      lift (Array.to_slice
        pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let output1 := index_mut_back s2
    let output2 ←
      Array.update output1 4#usize
        pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_VERSION
    let i := read_discriminant result.transition_kind
    let i1 ← lift (UScalar.cast .U8 i)
    let output3 ← Array.update output2 5#usize i1
    let output4 ←
      Array.update output3 6#usize
        pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
    let output5 ← Array.update output4 7#usize result.output_lane
    let (s3, index_mut_back1) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output5
        {
          start := pool_v1.pair_forest_terminal.RESULT_MASTER_OFFSET,
          «end» := pool_v1.pair_forest_terminal.RESULT_SELECTED_LANE_OFFSET
        }
    let s4 ← lift (Array.to_slice result.master_account)
    let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
    let output6 := index_mut_back1 s5
    let (s6, index_mut_back2) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output6
        {
          start := pool_v1.pair_forest_terminal.RESULT_SELECTED_LANE_OFFSET,
          «end» := pool_v1.pair_forest_terminal.RESULT_NULLIFIER_OFFSET
        }
    let s7 ← lift (Array.to_slice result.selected_lane_account)
    let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
    let output7 := index_mut_back2 s8
    let (s9, index_mut_back3) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output7
        {
          start := pool_v1.pair_forest_terminal.RESULT_NULLIFIER_OFFSET,
          «end» := pool_v1.pair_forest_terminal.RESULT_AFTERSTATE_OFFSET
        }
    let a ← digest result.nullifier
    let s10 ← lift (Array.to_slice a)
    let s11 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s9 s10
    let output8 := index_mut_back3 s11
    let (s12, index_mut_back4) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) output8
        { start := pool_v1.pair_forest_terminal.RESULT_AFTERSTATE_OFFSET }
    let r1 ←
      after result.verified_afterstate
    let r2 ←
      core.result.Result.map_err
        pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_result_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairForestTerminalFormatErrorV1
        r1 ()
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let s13 ← lift (Array.to_slice val)
      let s14 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s12 s13
      let output9 := index_mut_back4 s14
      ok (core.result.Result.Ok output9)
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (Array Std.U8 792#usize) (core.convert.FromSame
        pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
        residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Array Std.U8 792#usize) (core.convert.FromSame
      pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
      residual

/-- Exact emitted-body substitution, including both error branches. Native
window/child-domain/frame certificates remain separate obligations. -/
theorem result_state_effects {State : Type} (record : Record) (state : State) :
    (run pool_v1.pair_forest_terminal.validate_result
      atomic_statement.encode_digest_canonical
      pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 record,
      state,([] : List Unit)) =
    (pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_result_v1 record,
      state,[]) := by rfl
#print axioms result_state_effects
end NEY_ResultEncoderOracle

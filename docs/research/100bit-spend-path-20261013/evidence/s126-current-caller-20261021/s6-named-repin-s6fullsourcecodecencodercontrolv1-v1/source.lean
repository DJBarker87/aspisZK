import S6FullSourceCodecV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6SourceCodec.Control
open AspisS6FiveUnrolledCodec
abbrev Statement := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev PE := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
/-- Literal successful-validation continuation from the complete source evaluator. -/
def afterValidation (statement : Statement) :
    Result (core.result.Result (Array U8 1880#usize) PE) := do
  let common ← aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common statement
  let output := Array.repeat 1880#usize 0#u8
  let (s, index_mut_back) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) output { «end» := 4#usize }
  let s1 ← lift (Array.to_slice aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC)
  let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
  let output1 := index_mut_back s2
  let output2 ← Array.update output1 4#usize aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_VERSION
  let pvtk ← aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.transition_kind statement
  let i := read_discriminant pvtk
  let i1 ← lift (UScalar.cast .U8 i)
  let output3 ← Array.update output2 5#usize i1
  let output4 ← Array.update output3 6#usize aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
  let output5 ← Array.update output4 7#usize common.output_lane
  let (s3, index_mut_back1) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output5 { start := aspis_statement.pool_v1.pair_forest_terminal.MASTER_OFFSET, «end» := aspis_statement.pool_v1.pair_forest_terminal.CHECKPOINT_ACCOUNT_OFFSET }
  let s4 ← lift (Array.to_slice common.master_account)
  let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
  let output6 := index_mut_back1 s5
  let (s6, index_mut_back2) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output6 { start := aspis_statement.pool_v1.pair_forest_terminal.CHECKPOINT_ACCOUNT_OFFSET, «end» := aspis_statement.pool_v1.pair_forest_terminal.SELECTED_LANE_ACCOUNT_OFFSET }
  let s7 ← lift (Array.to_slice common.checkpoint_account)
  let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
  let output7 := index_mut_back2 s8
  let (s9, index_mut_back3) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output7 { start := aspis_statement.pool_v1.pair_forest_terminal.SELECTED_LANE_ACCOUNT_OFFSET, «end» := aspis_statement.pool_v1.pair_forest_terminal.CHECKPOINT_SEQUENCE_OFFSET }
  let s10 ← lift (Array.to_slice common.selected_lane_account)
  let s11 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s9 s10
  let output8 := index_mut_back3 s11
  let (s12, index_mut_back4) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output8 { start := aspis_statement.pool_v1.pair_forest_terminal.CHECKPOINT_SEQUENCE_OFFSET, «end» := aspis_statement.pool_v1.pair_forest_terminal.HISTORICAL_ANCHOR_OFFSET }
  let a ← lift (core.num.U64.to_le_bytes common.checkpoint_sequence)
  let s13 ← lift (Array.to_slice a)
  let s14 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s12 s13
  let output9 := index_mut_back4 s14
  let (s15, index_mut_back5) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output9 { start := aspis_statement.pool_v1.pair_forest_terminal.HISTORICAL_ANCHOR_OFFSET, «end» := aspis_statement.pool_v1.pair_forest_terminal.LATE_STATEMENT_OFFSET }
  let a1 ← aspis_statement.atomic_statement.encode_digest_canonical common.historical_global_anchor
  let s16 ← lift (Array.to_slice a1)
  let s17 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s15 s16
  let output10 := index_mut_back5 s17
  let i2 ← aspis_statement.pool_v1.pair_forest_terminal.PAYMENT_STATEMENT_OFFSET
  let (s18, index_mut_back6) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output10 { start := aspis_statement.pool_v1.pair_forest_terminal.LATE_STATEMENT_OFFSET, «end» := i2 }
  let (r1, s19) ← aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1 common.lane_transition s18
  let r2 ← core.result.Result.map_err aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1 r1 ()
  let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
  match cf1 with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let output11 := index_mut_back6 s19
    match statement with
    | aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.PrivateTransfer _ public1 =>
      let r3 ← aspis_statement.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1 public1
      let r4 ← core.result.Result.map_err aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1 r3 ()
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r4
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val => let (s20, index_mut_back7) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) output11 { start := i2 }
                                                          let s21 ← lift (Array.to_slice val)
                                                          let s22 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s20 s21
                                                          let output12 := index_mut_back7 s22
                                                          ok (core.result.Result.Ok output12)
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual (Array Std.U8 1880#usize) (core.convert.FromSame aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual
    | aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.Withdrawal _ public1 =>
      let r3 ← aspis_statement.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 public1
      let r4 ← core.result.Result.map_err aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1 r3 ()
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r4
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val => let (s20, index_mut_back7) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) output11 { start := i2 }
                                                          let s21 ← lift (Array.to_slice val)
                                                          let s22 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s20 s21
                                                          let output12 := index_mut_back7 s22
                                                          ok (core.result.Result.Ok output12)
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual (Array Std.U8 1880#usize) (core.convert.FromSame aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual (Array Std.U8 1880#usize) (core.convert.FromSame aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual

/-- Complete Result factorization of the actual emitted outer encoder.
No child success, canonicality, output or validation premise. -/
theorem encoder_control (statement : Statement) :
    encode statement = (do
      let valid ← aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 statement
      match valid with
      | .Err e => ok (.Err e)
      | .Ok () => afterValidation statement) := by
  unfold encode aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1 afterValidation
  cases hv : aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 statement with
  | fail e => rfl
  | div => rfl
  | ok valid =>
    cases valid with
    | Err e => rfl
    | Ok value => cases value; rfl

theorem encoder_rejects (statement : Statement) (error : PE)
    (h : aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 statement=ok (.Err error)) :
    encode statement=ok (.Err error) := by
  rw [encoder_control,h,bind_tc_ok]

theorem encoder_success_validates (statement : Statement)
    (out : Array U8 1880#usize) (h : encode statement=ok (.Ok out)) :
    aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 statement=ok (.Ok ()) ∧ afterValidation statement=ok (.Ok out) := by
  rw [encoder_control] at h
  cases hv : aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 statement with
  | fail e => rw [hv,bind_tc_fail] at h;cases h
  | div => rw [hv,bind_tc_div] at h;cases h
  | ok valid =>
    rw [hv,bind_tc_ok] at h
    cases valid with
    | Err e => cases h
    | Ok value => cases value;exact ⟨rfl,h⟩

#print axioms encoder_control
#print axioms encoder_rejects
#print axioms encoder_success_validates
end AspisS6SourceCodec.Control

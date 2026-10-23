import S6FullForestEncoderTypesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error






noncomputable section

namespace AspisS6FullForestEncoder

structure Ops where
 digest : Array aspis_core.field.M31 8#usize → Result (Array U8 32#usize)
 validate : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 →
   Result (core.result.Result Unit aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
 withdrawal : aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 →
   Result (core.result.Result (Array U8 216#usize) aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError)
 transfer : aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 →
   Result (core.result.Result (Array U8 216#usize) aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError)
 late : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 → Slice U8 →
   Result ((core.result.Result Unit aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) × Slice U8)




def core.result.Result.map_err
  {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
  core.ops.function.FnOnce O E F) (self : core.result.Result T E) (op : O) :
  Result (core.result.Result T F)
  := do
  match self with
  | core.result.Result.Ok t => ok (core.result.Result.Ok t)
  | core.result.Result.Err e =>
    let t ← opsfunctionFnOnceOTupleEFInst.call_once op e
    ok (core.result.Result.Err t)



def aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION : Std.U8 :=
  1#u8



def
  aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC
  : Array Std.U8 4#usize :=
  Array.make 4#usize [ 65#u8, 83#u8, 70#u8, 56#u8 ]



def
  aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_VERSION
  : Std.U8 :=
  1#u8



def aspis_statement.pool_v1.pair_forest_terminal.MASTER_OFFSET : Std.Usize :=
  8#usize



def aspis_statement.pool_v1.pair_forest_terminal.CHECKPOINT_ACCOUNT_OFFSET
  : Std.Usize :=
  40#usize



def aspis_statement.pool_v1.pair_forest_terminal.SELECTED_LANE_ACCOUNT_OFFSET
  : Std.Usize :=
  72#usize



def aspis_statement.pool_v1.pair_forest_terminal.CHECKPOINT_SEQUENCE_OFFSET
  : Std.Usize :=
  104#usize



def aspis_statement.pool_v1.pair_forest_terminal.HISTORICAL_ANCHOR_OFFSET
  : Std.Usize :=
  112#usize



def aspis_statement.pool_v1.pair_forest_terminal.LATE_STATEMENT_OFFSET
  : Std.Usize :=
  144#usize



def
  aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES
  : Std.Usize :=
  32#usize



def aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
  : Std.Usize :=
  800#usize



def
  aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
  : Std.Usize :=
  680#usize



def
  aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
  : Result Std.Usize :=
  8#usize +
    aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES



def
  aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES
  : Result Std.Usize := do
  let i ←
    aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES
      +
      aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
  let i1 ←
    aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
  i + i1



def aspis_statement.pool_v1.pair_forest_terminal.PAYMENT_STATEMENT_OFFSET
  : Result Std.Usize := do
  let i ←
    aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES
  aspis_statement.pool_v1.pair_forest_terminal.LATE_STATEMENT_OFFSET + i



def
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common
  (self :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1)
  :
  Result
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1
  := do
  match self with
  |
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.PrivateTransfer
    common _ =>
    ok common
  |
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.Withdrawal
    common _ =>
    ok common



def
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.transition_kind
  (self :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1)
  :
  Result aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind
  := do
  match self with
  |
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.PrivateTransfer
    _ _ =>
    ok
      aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer
  |
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.Withdrawal
    _ _ =>
    ok
      aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind.Withdrawal



def
  aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1.call_once
  (c :
  aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1.closure_1)
  (tupled_args :
  aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError) :
  Result
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  := do
  ok
    (aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.Payment
    tupled_args)



def
  aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1
  : core.ops.function.FnOnce
  aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1.closure_1
  aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  := {
  call_once :=
    aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1.call_once
}



def
  aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1.call_once
  (c :
  aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1.closure)
  (tupled_args :
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1)
  :
  Result
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  := do
  ok
    (aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.LaneTransition
    tupled_args)



def
  aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1
  : core.ops.function.FnOnce
  aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1.closure
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  := {
  call_once :=
    aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1.call_once
}



def aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1 (ops : Ops)
  (statement :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1)
  :
  Result (core.result.Result (Array Std.U8 1880#usize)
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  := do
  let r ←
    ops.validate
      statement
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let common ←
      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common
        statement
    let output := Array.repeat 1880#usize 0#u8
    let (s, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) output
        { «end» := 4#usize }
    let s1 ←
      lift (Array.to_slice
        aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let output1 := index_mut_back s2
    let output2 ←
      Array.update output1 4#usize
        aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_VERSION
    let pvtk ←
      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.transition_kind
        statement
    let i := read_discriminant pvtk
    let i1 ← lift (UScalar.cast .U8 i)
    let output3 ← Array.update output2 5#usize i1
    let output4 ←
      Array.update output3 6#usize
        aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
    let output5 ← Array.update output4 7#usize common.output_lane
    let (s3, index_mut_back1) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output5
        {
          start := aspis_statement.pool_v1.pair_forest_terminal.MASTER_OFFSET,
          «end» :=
            aspis_statement.pool_v1.pair_forest_terminal.CHECKPOINT_ACCOUNT_OFFSET
        }
    let s4 ← lift (Array.to_slice common.master_account)
    let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
    let output6 := index_mut_back1 s5
    let (s6, index_mut_back2) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output6
        {
          start :=
            aspis_statement.pool_v1.pair_forest_terminal.CHECKPOINT_ACCOUNT_OFFSET,
          «end» :=
            aspis_statement.pool_v1.pair_forest_terminal.SELECTED_LANE_ACCOUNT_OFFSET
        }
    let s7 ← lift (Array.to_slice common.checkpoint_account)
    let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
    let output7 := index_mut_back2 s8
    let (s9, index_mut_back3) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output7
        {
          start :=
            aspis_statement.pool_v1.pair_forest_terminal.SELECTED_LANE_ACCOUNT_OFFSET,
          «end» :=
            aspis_statement.pool_v1.pair_forest_terminal.CHECKPOINT_SEQUENCE_OFFSET
        }
    let s10 ← lift (Array.to_slice common.selected_lane_account)
    let s11 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s9 s10
    let output8 := index_mut_back3 s11
    let (s12, index_mut_back4) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output8
        {
          start :=
            aspis_statement.pool_v1.pair_forest_terminal.CHECKPOINT_SEQUENCE_OFFSET,
          «end» :=
            aspis_statement.pool_v1.pair_forest_terminal.HISTORICAL_ANCHOR_OFFSET
        }
    let a ← lift (core.num.U64.to_le_bytes common.checkpoint_sequence)
    let s13 ← lift (Array.to_slice a)
    let s14 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s12 s13
    let output9 := index_mut_back4 s14
    let (s15, index_mut_back5) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output9
        {
          start :=
            aspis_statement.pool_v1.pair_forest_terminal.HISTORICAL_ANCHOR_OFFSET,
          «end» :=
            aspis_statement.pool_v1.pair_forest_terminal.LATE_STATEMENT_OFFSET
        }
    let a1 ←
      ops.digest
        common.historical_global_anchor
    let s16 ← lift (Array.to_slice a1)
    let s17 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s15 s16
    let output10 := index_mut_back5 s17
    let i2 ←
      aspis_statement.pool_v1.pair_forest_terminal.PAYMENT_STATEMENT_OFFSET
    let (s18, index_mut_back6) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output10
        {
          start :=
            aspis_statement.pool_v1.pair_forest_terminal.LATE_STATEMENT_OFFSET,
          «end» := i2
        }
    let (r1, s19) ←
      ops.late
        common.lane_transition s18
    let r2 ←
      core.result.Result.map_err
        aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1
        r1 ()
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let output11 := index_mut_back6 s19
      match statement with
      |
        aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.PrivateTransfer
        _ public1 =>
        let r3 ←
          ops.transfer
            public1
        let r4 ←
          core.result.Result.map_err
            aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1
            r3 ()
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r4
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val =>
          let (s20, index_mut_back7) ←
            core.array.Array.index_mut (core.ops.index.IndexMutSlice
              (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) output11
              { start := i2 }
          let s21 ← lift (Array.to_slice val)
          let s22 ←
            core.slice.Slice.copy_from_slice core.marker.CopyU8 s20 s21
          let output12 := index_mut_back7 s22
          ok (core.result.Result.Ok output12)
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (Array Std.U8 1880#usize) (core.convert.FromSame
            aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
            residual
      |
        aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.Withdrawal
        _ public1 =>
        let r3 ←
          ops.withdrawal
            public1
        let r4 ←
          core.result.Result.map_err
            aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1
            r3 ()
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r4
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val =>
          let (s20, index_mut_back7) ←
            core.array.Array.index_mut (core.ops.index.IndexMutSlice
              (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) output11
              { start := i2 }
          let s21 ← lift (Array.to_slice val)
          let s22 ←
            core.slice.Slice.copy_from_slice core.marker.CopyU8 s20 s21
          let output12 := index_mut_back7 s22
          ok (core.result.Result.Ok output12)
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (Array Std.U8 1880#usize) (core.convert.FromSame
            aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
            residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (Array Std.U8 1880#usize) (core.convert.FromSame
        aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
        residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Array Std.U8 1880#usize) (core.convert.FromSame
      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
      residual


def encode (ops : Ops)
  (statement :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1)
  :
  Result (core.result.Result (Array Std.U8 1880#usize)
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  := do
  aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1 ops
    statement

end AspisS6FullForestEncoder

#print axioms AspisS6FullForestEncoder.aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1
#print axioms AspisS6FullForestEncoder.encode

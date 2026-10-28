import NDO_JHb_S2K_ResultAdmission
import NDO_JHb_S2K_ByteEquality
import NDO_JHb_S2K_ResultEvent

/-! Actual extracted result validator; only names/duplicate dependencies adapted.
Opaque encoder declarations are replaced by the already-proved exact definitions
on identical carriers. No new opaque constant or successful-child premise. -/
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
namespace AspisR1TerminalDecoder

/-- [aspis_statement::pool_v1::pair_forest_terminal::encode_pool_v1_pair_forest_terminal_result_v1::closure]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 595:21-595:85 -/
@[reducible]
def pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_result_v1.closure
  :=
Unit

/-- Trait implementation: [core::array::equality::{impl core::cmp::PartialEq<[U; N]> for [T; N]}]
    Source: '/rustc/library/core/src/array/equality.rs', lines 5:0-7:28
    Name pattern: [core::cmp::PartialEq<[@T; @N], [@U; @N]>] -/
@[reducible, rust_trait_impl "core::cmp::PartialEq<[@T; @N], [@U; @N]>"]
def Array.Insts.CoreCmpPartialEqArray {T : Type} {U : Type} (N : Std.Usize)
  (cmpPartialEqInst : core.cmp.PartialEq T U) : core.cmp.PartialEq (Array T N)
  (Array U N) := {
  eq := core.array.equality.PartialEqArray.eq cmpPartialEqInst
  ne := core.array.equality.PartialEqArray.ne cmpPartialEqInst
}

/-- [aspis_statement::pool_v1::historical_anchor::{impl core::cmp::PartialEq<aspis_statement::pool_v1::historical_anchor::PoolV1TransitionKind> for aspis_statement::pool_v1::historical_anchor::PoolV1TransitionKind}::eq]:
    Source: 'crates/aspis-statement/src/pool_v1/historical_anchor.rs', lines 30:29-30:38
    Visibility: public -/
def
  pool_v1.historical_anchor.PoolV1TransitionKind.Insts.CoreCmpPartialEqPoolV1TransitionKind.eq
  (self : pool_v1.historical_anchor.PoolV1TransitionKind)
  (other : pool_v1.historical_anchor.PoolV1TransitionKind) :
  Result Bool
  := do
  let self1 := read_discriminant self
  let other1 := read_discriminant other
  ok (self1 = other1)

/-- Trait implementation: [aspis_statement::pool_v1::historical_anchor::{impl core::cmp::PartialEq<aspis_statement::pool_v1::historical_anchor::PoolV1TransitionKind> for aspis_statement::pool_v1::historical_anchor::PoolV1TransitionKind}]
    Source: 'crates/aspis-statement/src/pool_v1/historical_anchor.rs', lines 30:29-30:38 -/
@[reducible]
impl_def
  pool_v1.historical_anchor.PoolV1TransitionKind.Insts.CoreCmpPartialEqPoolV1TransitionKind
  : core.cmp.PartialEq pool_v1.historical_anchor.PoolV1TransitionKind
  pool_v1.historical_anchor.PoolV1TransitionKind := {
  eq :=
    pool_v1.historical_anchor.PoolV1TransitionKind.Insts.CoreCmpPartialEqPoolV1TransitionKind.eq
  ne := core.cmp.PartialEq.ne.trait_default
    pool_v1.historical_anchor.PoolV1TransitionKind.Insts.CoreCmpPartialEqPoolV1TransitionKind
}

/-- [aspis_statement::pool_v1::pair_forest_terminal::POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 30:0-30:72
    Visibility: public -/
@[global_simps, irreducible]
def pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC
  : Array Std.U8 4#usize :=
  Array.make 4#usize [ 65#u8, 83#u8, 82#u8, 56#u8 ]

/-- [aspis_statement::pool_v1::pair_forest_terminal::RESULT_MASTER_OFFSET]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 52:0-52:38 -/
@[global_simps, irreducible]
def pool_v1.pair_forest_terminal.RESULT_MASTER_OFFSET : Std.Usize := 8#usize

/-- [aspis_statement::pool_v1::pair_forest_terminal::RESULT_SELECTED_LANE_OFFSET]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 53:0-53:46 -/
@[global_simps, irreducible]
def pool_v1.pair_forest_terminal.RESULT_SELECTED_LANE_OFFSET : Std.Usize :=
  40#usize

/-- [aspis_statement::pool_v1::pair_forest_terminal::RESULT_NULLIFIER_OFFSET]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 54:0-54:42 -/
@[global_simps, irreducible]
def pool_v1.pair_forest_terminal.RESULT_NULLIFIER_OFFSET : Std.Usize :=
  72#usize

/-- [aspis_statement::pool_v1::pair_forest_terminal::RESULT_AFTERSTATE_OFFSET]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 55:0-55:44 -/
@[global_simps, irreducible]
def pool_v1.pair_forest_terminal.RESULT_AFTERSTATE_OFFSET : Std.Usize :=
  104#usize

/-- [aspis_statement::pool_v1::pair_forest_terminal::{aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalStatementV1}::transition_kind]:
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 140:4-145:5
    Visibility: public -/
def
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.transition_kind
  (self : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) :
  Result pool_v1.historical_anchor.PoolV1TransitionKind
  := do
  match self with
  |
    pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.PrivateTransfer
    _ _ =>
    ok pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer
  | pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.Withdrawal
    _ _ =>
    ok pool_v1.historical_anchor.PoolV1TransitionKind.Withdrawal

/-- [aspis_statement::pool_v1::pair_forest_terminal::{aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalStatementV1}::nullifier]:
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 148:4-153:5
    Visibility: public -/
def pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.nullifier
  (self : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) :
  Result (Array aspis_core.field.M31 8#usize)
  := do
  match self with
  |
    pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.PrivateTransfer
    _ public1 =>
    ok public1.nullifier
  | pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.Withdrawal
    _ public1 =>
    ok public1.nullifier

/-- [aspis_statement::pool_v1::pair_terminal::{impl core::cmp::PartialEq<aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1> for aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1}::eq]:
    Source: 'crates/aspis-statement/src/pool_v1/pair_terminal.rs', lines 115:29-115:38
    Visibility: public -/
def
  pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1.Insts.CoreCmpPartialEqPoolV1PairVerifiedAfterstateV1.eq
  (self : pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1)
  (other : pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) :
  Result Bool
  := do
  if self.next_pair_index = other.next_pair_index
  then
    let b ←
      core.array.equality.PartialEqArray.eq
        aspis_core.field.M31.Insts.CoreCmpPartialEqM31 self.next_root
        other.next_root
    if b
    then
      core.array.equality.PartialEqArray.eq (Array.Insts.CoreCmpPartialEqArray
        8#usize aspis_core.field.M31.Insts.CoreCmpPartialEqM31)
        self.next_frontier other.next_frontier
    else ok false
  else ok false

/-- Trait implementation: [aspis_statement::pool_v1::pair_terminal::{impl core::cmp::PartialEq<aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1> for aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1}]
    Source: 'crates/aspis-statement/src/pool_v1/pair_terminal.rs', lines 115:29-115:38 -/
@[reducible]
impl_def
  pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1.Insts.CoreCmpPartialEqPoolV1PairVerifiedAfterstateV1
  : core.cmp.PartialEq pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
  pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 := {
  eq :=
    pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1.Insts.CoreCmpPartialEqPoolV1PairVerifiedAfterstateV1.eq
  ne := core.cmp.PartialEq.ne.trait_default
    pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1.Insts.CoreCmpPartialEqPoolV1PairVerifiedAfterstateV1
}

/-- [aspis_statement::pool_v1::pair_forest_terminal::validate_pool_v1_pair_forest_terminal_result_against_statement_v1]:
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 557:0-574:1
    Visibility: public -/
def
  pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_result_against_statement_v1
  (statement :
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1)
  (result : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1) :
  Result (core.result.Result Unit
    pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  := do
  let r ←
    pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
      statement
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let r1 ← pool_v1.pair_forest_terminal.validate_result result
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let common ←
        pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common
          statement
      let pvtk ←
        pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.transition_kind
          statement
      let b ←
        core.cmp.PartialEq.ne.trait_default
          pool_v1.historical_anchor.PoolV1TransitionKind.Insts.CoreCmpPartialEqPoolV1TransitionKind
          result.transition_kind pvtk
      if b
      then
        ok (core.result.Result.Err
          pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.ResultBindingMismatch)
      else
        let b1 ←
          core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
            result.master_account common.master_account
        if b1
        then
          ok (core.result.Result.Err
            pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.ResultBindingMismatch)
        else
          let b2 ←
            core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
              result.selected_lane_account common.selected_lane_account
          if b2
          then
            ok (core.result.Result.Err
              pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.ResultBindingMismatch)
          else
            if result.output_lane != common.output_lane
            then
              ok (core.result.Result.Err
                pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.ResultBindingMismatch)
            else
              let a ←
                pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.nullifier
                  statement
              let b3 ←
                core.array.equality.PartialEqArray.ne
                  aspis_core.field.M31.Insts.CoreCmpPartialEqM31
                  result.nullifier a
              if b3
              then
                ok (core.result.Result.Err
                  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.ResultBindingMismatch)
              else
                let b4 ←
                  core.cmp.PartialEq.ne.trait_default
                    pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1.Insts.CoreCmpPartialEqPoolV1PairVerifiedAfterstateV1
                    result.verified_afterstate
                    common.lane_transition.candidate_afterstate
                if b4
                then
                  ok (core.result.Result.Err
                    pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.ResultBindingMismatch)
                else ok (core.result.Result.Ok ())
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Unit (core.convert.FromSame
        pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
        residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame
      pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
      residual

/-- [aspis_statement::pool_v1::pair_forest_terminal::encode_pool_v1_pair_forest_terminal_result_v1::{impl core::ops::function::FnOnce<(aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifierTransportErrorV1,), aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalFormatErrorV1> for aspis_statement::pool_v1::pair_forest_terminal::encode_pool_v1_pair_forest_terminal_result_v1::closure}::call_once]:
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 595:21-595:85 -/
def
  pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_result_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairForestTerminalFormatErrorV1.call_once
  (c :
  pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_result_v1.closure)
  (tupled_args : pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) :
  Result pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  := do
  ok
    (pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.Afterstate
    tupled_args)

/-- Trait implementation: [aspis_statement::pool_v1::pair_forest_terminal::encode_pool_v1_pair_forest_terminal_result_v1::{impl core::ops::function::FnOnce<(aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifierTransportErrorV1,), aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalFormatErrorV1> for aspis_statement::pool_v1::pair_forest_terminal::encode_pool_v1_pair_forest_terminal_result_v1::closure}]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 595:21-595:85 -/
@[reducible]
def
  pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_result_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairForestTerminalFormatErrorV1
  : core.ops.function.FnOnce
  pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_result_v1.closure
  pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1 := {
  call_once :=
    pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_result_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairForestTerminalFormatErrorV1.call_once
}

/-- [aspis_statement::pool_v1::pair_forest_terminal::encode_pool_v1_pair_forest_terminal_result_v1]:
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 576:0-598:1
    Visibility: public -/
def pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_result_v1
  (result : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1) :
  Result (core.result.Result (Array Std.U8 792#usize)
    pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  := do
  let r ← pool_v1.pair_forest_terminal.validate_result result
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
    let a ← atomic_statement.encode_digest_canonical result.nullifier
    let s10 ← lift (Array.to_slice a)
    let s11 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s9 s10
    let output8 := index_mut_back3 s11
    let (s12, index_mut_back4) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) output8
        { start := pool_v1.pair_forest_terminal.RESULT_AFTERSTATE_OFFSET }
    let r1 ←
      pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1
        result.verified_afterstate
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

#print axioms pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_result_v1
#print axioms pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_result_against_statement_v1
end AspisR1TerminalDecoder

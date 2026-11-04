import Lean
import NFY_Part031
import NFY_Part020
import NFY_Part023
import RPz7_S6NativeSnapshotReadArrayV1
import NFY_Part024

-- BEGIN copied JHb_S2K_Equality: lean/JHb_S2K_Equality.lean

/-! Symbolic reflexivity for source array comparisons; no concrete arrays reduced. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.Equality

theorem array_self {T : Type} (cmp : core.cmp.PartialEq T T)
    (same : ∀ x, cmp.ne x x = ok false) {n : Usize} (a : Array T n) :
    core.array.equality.PartialEqArray.eq cmp a a = ok true := by
  have list_self : ∀ xs : List T,
      List.allM (fun (x,y) => do let b ← cmp.ne x y; ok (¬ b))
        (List.zip xs xs) = ok true := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.zip_cons_cons,List.allM,same,bind_tc_ok]; exact ih
  unfold core.array.equality.PartialEqArray.eq
  rw [if_pos rfl]
  exact list_self a.val

#print axioms array_self
end AspisR1.S2K.Equality
-- END copied JHb_S2K_Equality
-- BEGIN copied JHb_S2K_ByteEquality: lean/JHb_S2K_ByteEquality.lean

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.Equality
open AspisR1TerminalDecoder

theorem array_ne_self {T : Type} (cmp : core.cmp.PartialEq T T)
    (same : ∀ x, cmp.ne x x = ok false) {n : Usize} (a : Array T n) :
    core.array.equality.PartialEqArray.ne cmp a a = ok false := by
  rw [core.array.equality.PartialEqArray.ne,array_self cmp same]
  rfl

theorem u8_ne_self (x : U8) : core.cmp.PartialEqU8.ne x x = ok false := by
  simp [core.cmp.PartialEqU8,core.cmp.impls.PartialEqU8.ne,liftFun2,lift]

theorem m31_ne_self (x : aspis_core.field.M31) :
    aspis_core.field.M31.Insts.CoreCmpPartialEqM31.ne x x = ok false := by
  simp [aspis_core.field.M31.Insts.CoreCmpPartialEqM31,
    core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
    aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq]


#print axioms array_ne_self
#print axioms u8_ne_self
#print axioms m31_ne_self
end AspisR1.S2K.Equality
-- END copied JHb_S2K_ByteEquality
-- BEGIN copied JHb_S2K_ResultWholeNative: lean/JHb_S2K_ResultWholeNative.lean

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
-- END copied JHb_S2K_ResultWholeNative
-- BEGIN copied JHb_S2K_ResultBinding: lean/JHb_S2K_ResultBinding.lean

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.ResultBinding
open AspisR1TerminalDecoder Equality StatementAdmission StatementChecks ResultAdmission
open pool_v1.pair_forest_terminal pool_v1.pair_terminal

theorem byte_array_ne_self {n : Usize} (a : Array U8 n) :
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 a a = ok false :=
  array_ne_self _ u8_ne_self a

theorem digest_ne_self {n : Usize} (a : Array aspis_core.field.M31 n) :
    core.array.equality.PartialEqArray.ne aspis_core.field.M31.Insts.CoreCmpPartialEqM31 a a = ok false :=
  array_ne_self _ m31_ne_self a

theorem afterstate_self (a : PoolV1PairVerifiedAfterstateV1) :
    PoolV1PairVerifiedAfterstateV1.Insts.CoreCmpPartialEqPoolV1PairVerifiedAfterstateV1.eq a a = ok true := by
  have root := array_self _ m31_ne_self a.next_root
  have frontier := array_self (Array.Insts.CoreCmpPartialEqArray 8#usize
    aspis_core.field.M31.Insts.CoreCmpPartialEqM31)
    (fun xs => digest_ne_self xs) a.next_frontier
  simp only [PoolV1PairVerifiedAfterstateV1.Insts.CoreCmpPartialEqPoolV1PairVerifiedAfterstateV1.eq,
    if_pos rfl,root,bind_tc_ok]
  exact frontier

theorem validated (s : Statement)
    (accepted : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    validate_pool_v1_pair_forest_terminal_result_against_statement_v1 s (value s) = ok (.Ok ()) := by
  have valid := ResultAdmission.validated s accepted
  simp only [validate_pool_v1_pair_forest_terminal_result_against_statement_v1,
    accepted,valid,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  cases s <;> simp [value,kind,common,nullifier,
    PoolV1PairForestTerminalStatementV1.common,
    PoolV1PairForestTerminalStatementV1.transition_kind,
    PoolV1PairForestTerminalStatementV1.nullifier,
    core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
    pool_v1.historical_anchor.PoolV1TransitionKind.Insts.CoreCmpPartialEqPoolV1TransitionKind.eq,
    byte_array_ne_self,digest_ne_self,afterstate_self]

#print axioms byte_array_ne_self
#print axioms digest_ne_self
#print axioms afterstate_self
#print axioms validated
end AspisR1.S2K.ResultBinding
-- END copied JHb_S2K_ResultBinding
-- BEGIN copied JHb_S2K_ResultPayload: lean/JHb_S2K_ResultPayload.lean

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.ResultPayload
open AspisR1TerminalDecoder StatementAdmission StatementChecks ResultAdmission
open pool_v1.pair_forest_terminal

def kindByte : Statement → U8
  | .PrivateTransfer _ _ => 1#u8
  | .Withdrawal _ _ => 2#u8

def bytes (s : Statement) : Array U8 792#usize :=
  ResultEncoding.stores (Array.repeat 792#usize 0#u8)
    (common s).master_account (common s).selected_lane_account
    (DigestBytes.bytes (nullifier s)) (kindByte s) (common s).output_lane
    (AfterstateEncoding.bytes (common s).lane_transition.candidate_afterstate)

theorem encoded (s : Statement)
    (accepted : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    encode_pool_v1_pair_forest_terminal_result_v1 (value s) = ok (.Ok (bytes s)) := by
  have valid := ResultAdmission.validated s accepted
  have payload := StatementAdmission.payload s accepted
  have digest := DigestBytes.exact (nullifier s)
  simp only [encode_pool_v1_pair_forest_terminal_result_v1,valid,
    bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  simp only [value] at digest payload ⊢
  rw [digest,payload]
  unfold bytes
  generalize Array.repeat 792#usize 0#u8 = output
  cases s <;> simp [value,kind,kindByte,common,nullifier,
    ResultEncoding.stores,POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC,
    POOL_V1_PAIR_FOREST_TERMINAL_VERSION,pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,
    RESULT_MASTER_OFFSET,RESULT_SELECTED_LANE_OFFSET,RESULT_NULLIFIER_OFFSET,RESULT_AFTERSTATE_OFFSET,
    core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,
    core.array.Array.index_mut,core.ops.index.IndexMutSlice,core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeToUsizeSlice,core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice,core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.index.SliceIndexRangeFromUsizeSlice,core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut,
    Array.to_slice,Array.from_slice,core.slice.Slice.copy_from_slice,
    Slice.length,Slice.len,Array.update,output.property,List.slice,lift]

  all_goals rfl

#print axioms encoded
end AspisR1.S2K.ResultPayload
-- END copied JHb_S2K_ResultPayload
-- BEGIN copied JHb_S2K_ResultHeader: lean/JHb_S2K_ResultHeader.lean

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.ResultHeader
open StatementAdmission

theorem take_setSlice_prefix {T : Type} (xs src : List T) (offset n : Nat)
    (before : n ≤ offset) (size : n ≤ xs.length) :
    (xs.setSlice! offset src).take n = xs.take n := by
  have room : n ≤ (xs.take offset).length := by simp only [List.length_take]; omega
  simp only [List.setSlice!]
  rw [List.append_assoc,List.take_append_of_le_length room,List.take_take,Nat.min_eq_left before]

theorem magic (s : Statement) :
    (ResultPayload.bytes s).val.take 4 = [65#u8,83#u8,82#u8,56#u8] := by
  unfold ResultPayload.bytes
  generalize Array.repeat 792#usize 0#u8 = output
  simp only [ResultEncoding.stores]
  simp [take_setSlice_prefix,List.take_set_of_le,output.property]
  simp [List.setSlice!,output.property]

#print axioms take_setSlice_prefix
#print axioms magic
end AspisR1.S2K.ResultHeader
-- END copied JHb_S2K_ResultHeader
-- BEGIN copied JFs_Cell00: lean/JFs_Cell00.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_Cell00
open Aeneas Aeneas.Std Result

def bytes : List U8 := [34#u8,8#u8,198#u8,55#u8,61#u8,211#u8,19#u8,178#u8,242#u8,118#u8,165#u8,45#u8,20#u8,254#u8,147#u8,25#u8,55#u8,157#u8,211#u8,124#u8,152#u8,170#u8,59#u8,88#u8,182#u8,77#u8,252#u8,152#u8,45#u8,26#u8,82#u8,63#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 8).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 8).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem source : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    NFY_JFx_NativeBytes.publicInput {start:=8#usize,«end»:=40#usize}=
    ok (NFY_JFu_PublicRange.segment 8 32 (by decide)) :=
  by
    have call:=NFY_JFu_PublicRange.read 8#usize 40#usize (by decide) (by decide)
    simpa only [show (8#usize).val=8 from rfl,
      show (40#usize).val=40 from rfl,Nat.reduceSub] using call

def value : Array U8 32#usize := ⟨bytes,length⟩

#print axioms length
#print axioms selected
#print axioms source
end AspisR1.NFY_JFs_Cell00
-- END copied JFs_Cell00
-- BEGIN copied JFs_Cell01: lean/JFs_Cell01.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_Cell01
open Aeneas Aeneas.Std Result

def bytes : List U8 := [196#u8,102#u8,84#u8,170#u8,104#u8,43#u8,219#u8,48#u8,186#u8,107#u8,137#u8,83#u8,94#u8,246#u8,77#u8,0#u8,95#u8,194#u8,23#u8,211#u8,45#u8,133#u8,134#u8,108#u8,194#u8,76#u8,167#u8,72#u8,207#u8,114#u8,192#u8,205#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 40).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 40).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem source : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    NFY_JFx_NativeBytes.publicInput {start:=40#usize,«end»:=72#usize}=
    ok (NFY_JFu_PublicRange.segment 40 32 (by decide)) :=
  by
    have call:=NFY_JFu_PublicRange.read 40#usize 72#usize (by decide) (by decide)
    simpa only [show (40#usize).val=40 from rfl,
      show (72#usize).val=72 from rfl,Nat.reduceSub] using call

def value : Array U8 32#usize := ⟨bytes,length⟩

#print axioms length
#print axioms selected
#print axioms source
end AspisR1.NFY_JFs_Cell01
-- END copied JFs_Cell01
-- BEGIN copied JFs_Cell02: lean/JFs_Cell02.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_Cell02
open Aeneas Aeneas.Std Result

def bytes : List U8 := [32#u8,73#u8,231#u8,207#u8,1#u8,77#u8,136#u8,117#u8,47#u8,206#u8,98#u8,125#u8,13#u8,237#u8,112#u8,176#u8,187#u8,122#u8,65#u8,248#u8,189#u8,141#u8,180#u8,25#u8,45#u8,142#u8,52#u8,8#u8,202#u8,78#u8,16#u8,28#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 72).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 72).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem source : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    NFY_JFx_NativeBytes.publicInput {start:=72#usize,«end»:=104#usize}=
    ok (NFY_JFu_PublicRange.segment 72 32 (by decide)) :=
  by
    have call:=NFY_JFu_PublicRange.read 72#usize 104#usize (by decide) (by decide)
    simpa only [show (72#usize).val=72 from rfl,
      show (104#usize).val=104 from rfl,Nat.reduceSub] using call

def value : Array U8 32#usize := ⟨bytes,length⟩

#print axioms length
#print axioms selected
#print axioms source
end AspisR1.NFY_JFs_Cell02
-- END copied JFs_Cell02
-- BEGIN copied JFs_Cell03: lean/JFs_Cell03.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_Cell03
open Aeneas Aeneas.Std Result

def bytes : List U8 := [42#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
theorem length : bytes.length=8 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 104).take 8=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 104).take 8=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem source : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    NFY_JFx_NativeBytes.publicInput {start:=104#usize,«end»:=112#usize}=
    ok (NFY_JFu_PublicRange.segment 104 8 (by decide)) :=
  by
    have call:=NFY_JFu_PublicRange.read 104#usize 112#usize (by decide) (by decide)
    simpa only [show (104#usize).val=104 from rfl,
      show (112#usize).val=112 from rfl,Nat.reduceSub] using call

def value : Array U8 8#usize := ⟨bytes,length⟩

#print axioms length
#print axioms selected
#print axioms source
end AspisR1.NFY_JFs_Cell03
-- END copied JFs_Cell03
-- BEGIN copied JFt_ReadArray: lean/JFt_ReadArray.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_ReadArray
open Aeneas Aeneas.Std Result WP

theorem source (off n : Nat) (bound : off+n≤1880) (N : Usize)
    (arr : Array U8 N) (selected : (NFY_JFx_NativeBytes.publicInput.val.drop off).take n=arr.val) :
    AspisS6NativeSnapshotReadArray.read_array N (NFY_JFu_PublicRange.segment off n bound)=ok arr := by
  have size : (NFY_JFu_PublicRange.segment off n bound).length=N.val := by
    change ((NFY_JFx_NativeBytes.publicInput.val.drop off).take n).length=N.val
    rw [selected,arr.property]
  obtain ⟨out,call,bytes⟩:=WP.spec_imp_exists
    (AspisS6NativeSnapshotReadArray.read_array_spec N (NFY_JFu_PublicRange.segment off n bound) size)
  have same : out=arr := Subtype.ext (bytes.trans selected)
  rw [same] at call
  exact call

#print axioms source
end AspisR1.NFY_JFt_ReadArray
-- END copied JFt_ReadArray
-- BEGIN copied JFs_LateWords: lean/JFs_LateWords.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_LateWords
open Aeneas Aeneas.Std Result

def a10 : Array U8 2#usize := ⟨(NFY_JFu_PublicMeta00.bytes.drop 10).take 2,by simp [NFY_JFu_PublicMeta00.bytes]⟩
theorem selected10 : (NFY_JFu_PublicRange.segment 154 2 (by decide)).val=a10.val :=
  NFY_JFt_LocalWindow.selected 144 32 10 2 (by decide) (by decide) _ NFY_JFu_PublicMeta00.selected
theorem read10 : AspisS6NativeSnapshotReadArray.read_array 2#usize
    (NFY_JFu_PublicRange.segment 154 2 (by decide))=ok a10 :=
  NFY_JFt_ReadArray.source _ _ _ _ _ selected10
theorem word10 : core.num.U16.from_le_bytes a10=32#u16 := by rfl
theorem cast10 : UScalar.cast .Usize 32#u16=32#usize := by scalar_tac

def a12 : Array U8 4#usize := ⟨(NFY_JFu_PublicMeta00.bytes.drop 12).take 4,by simp [NFY_JFu_PublicMeta00.bytes]⟩
theorem selected12 : (NFY_JFu_PublicRange.segment 156 4 (by decide)).val=a12.val :=
  NFY_JFt_LocalWindow.selected 144 32 12 4 (by decide) (by decide) _ NFY_JFu_PublicMeta00.selected
theorem read12 : AspisS6NativeSnapshotReadArray.read_array 4#usize
    (NFY_JFu_PublicRange.segment 156 4 (by decide))=ok a12 :=
  NFY_JFt_ReadArray.source _ _ _ _ _ selected12
theorem word12 : core.num.U32.from_le_bytes a12=800#u32 := by rfl
theorem cast12 : UScalar.cast .Usize 800#u32=800#usize := by scalar_tac

def a16 : Array U8 4#usize := ⟨(NFY_JFu_PublicMeta00.bytes.drop 16).take 4,by simp [NFY_JFu_PublicMeta00.bytes]⟩
theorem selected16 : (NFY_JFu_PublicRange.segment 160 4 (by decide)).val=a16.val :=
  NFY_JFt_LocalWindow.selected 144 32 16 4 (by decide) (by decide) _ NFY_JFu_PublicMeta00.selected
theorem read16 : AspisS6NativeSnapshotReadArray.read_array 4#usize
    (NFY_JFu_PublicRange.segment 160 4 (by decide))=ok a16 :=
  NFY_JFt_ReadArray.source _ _ _ _ _ selected16
theorem word16 : core.num.U32.from_le_bytes a16=688#u32 := by rfl
theorem cast16 : UScalar.cast .Usize 688#u32=688#usize := by scalar_tac

def a20 : Array U8 4#usize := ⟨(NFY_JFu_PublicMeta00.bytes.drop 20).take 4,by simp [NFY_JFu_PublicMeta00.bytes]⟩
theorem selected20 : (NFY_JFu_PublicRange.segment 164 4 (by decide)).val=a20.val :=
  NFY_JFt_LocalWindow.selected 144 32 20 4 (by decide) (by decide) _ NFY_JFu_PublicMeta00.selected
theorem read20 : AspisS6NativeSnapshotReadArray.read_array 4#usize
    (NFY_JFu_PublicRange.segment 164 4 (by decide))=ok a20 :=
  NFY_JFt_ReadArray.source _ _ _ _ _ selected20
theorem word20 : core.num.U32.from_le_bytes a20=1520#u32 := by rfl
theorem cast20 : UScalar.cast .Usize 1520#u32=1520#usize := by scalar_tac

#print axioms selected10
#print axioms read10
#print axioms word10
#print axioms cast10
#print axioms selected12
#print axioms read12
#print axioms word12
#print axioms cast12
#print axioms selected16
#print axioms read16
#print axioms word16
#print axioms cast16
#print axioms selected20
#print axioms read20
#print axioms word20
#print axioms cast20
end AspisR1.NFY_JFs_LateWords
-- END copied JFs_LateWords
-- BEGIN copied JFu_PublicMeta06: lean/JFu_PublicMeta06.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicMeta06
open Aeneas Aeneas.Std Result

def bytes : List U8 := [65#u8,83#u8,74#u8,65#u8,1#u8,1#u8,1#u8,1#u8,14#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
theorem length : bytes.length=16 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 976).take 16=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 976).take 16=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem source : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    NFY_JFx_NativeBytes.publicInput {start:=976#usize,«end»:=992#usize}=
    ok (NFY_JFu_PublicRange.segment 976 16 (by decide)) :=
  by
    have call:=NFY_JFu_PublicRange.read 976#usize 992#usize (by decide) (by decide)
    simpa only [show (976#usize).val=976 from rfl,
      show (992#usize).val=992 from rfl,Nat.reduceSub] using call

#print axioms length
#print axioms selected
#print axioms source
end AspisR1.NFY_JFu_PublicMeta06
-- END copied JFu_PublicMeta06

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))

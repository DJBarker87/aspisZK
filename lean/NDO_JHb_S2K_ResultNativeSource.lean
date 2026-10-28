import NDO_JHb_S2K_ResultEvent

/-! Actual extracted result validator; only names/duplicate dependencies adapted.
Opaque encoder declarations are replaced by the already-proved exact definitions
on identical carriers. No new opaque constant or successful-child premise. -/
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
namespace AspisR1TerminalDecoder

/-- [aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalResultV1]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 169:0-176:1
    Visibility: public -/
structure pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1 where
  transition_kind : pool_v1.historical_anchor.PoolV1TransitionKind
  master_account : Array Std.U8 32#usize
  selected_lane_account : Array Std.U8 32#usize
  output_lane : Std.U8
  nullifier : Array aspis_core.field.M31 8#usize
  verified_afterstate : pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1

/-- [aspis_statement::pool_v1::pair_forest_terminal::validate_result::closure#1]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 549:17-549:81 -/
@[reducible]
def pool_v1.pair_forest_terminal.validate_result.closure_1 := Unit

/-- [aspis_statement::pool_v1::pair_forest_terminal::validate_result::closure]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 544:17-544:78 -/
@[reducible]
def pool_v1.pair_forest_terminal.validate_result.closure := Unit

/-- [aspis_statement::pool_v1::pair_forest_terminal::validate_result::{impl core::ops::function::FnOnce<(aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifierTransportErrorV1,), aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalFormatErrorV1> for aspis_statement::pool_v1::pair_forest_terminal::validate_result::closure#1}::call_once]:
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 549:17-549:81 -/
def
  pool_v1.pair_forest_terminal.validate_result.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairForestTerminalFormatErrorV1.call_once
  (c : pool_v1.pair_forest_terminal.validate_result.closure_1)
  (tupled_args : pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) :
  Result pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  := do
  ok
    (pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.Afterstate
    tupled_args)

/-- Trait implementation: [aspis_statement::pool_v1::pair_forest_terminal::validate_result::{impl core::ops::function::FnOnce<(aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifierTransportErrorV1,), aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalFormatErrorV1> for aspis_statement::pool_v1::pair_forest_terminal::validate_result::closure#1}]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 549:17-549:81 -/
@[reducible]
def
  pool_v1.pair_forest_terminal.validate_result.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairForestTerminalFormatErrorV1
  : core.ops.function.FnOnce
  pool_v1.pair_forest_terminal.validate_result.closure_1
  pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1 := {
  call_once :=
    pool_v1.pair_forest_terminal.validate_result.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairForestTerminalFormatErrorV1.call_once
}

/-- [aspis_statement::pool_v1::pair_forest_terminal::validate_result::{impl core::ops::function::FnOnce<(aspis_statement::pool_v1::pair_forest_accounts::PoolV1PairForestAccountErrorV1,), aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalFormatErrorV1> for aspis_statement::pool_v1::pair_forest_terminal::validate_result::closure}::call_once]:
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 544:17-544:78 -/
def
  pool_v1.pair_forest_terminal.validate_result.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1.call_once
  (c : pool_v1.pair_forest_terminal.validate_result.closure)
  (tupled_args : pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1) :
  Result pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  := do
  ok
    (pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.Account
    tupled_args)

/-- Trait implementation: [aspis_statement::pool_v1::pair_forest_terminal::validate_result::{impl core::ops::function::FnOnce<(aspis_statement::pool_v1::pair_forest_accounts::PoolV1PairForestAccountErrorV1,), aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalFormatErrorV1> for aspis_statement::pool_v1::pair_forest_terminal::validate_result::closure}]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 544:17-544:78 -/
@[reducible]
def
  pool_v1.pair_forest_terminal.validate_result.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1
  : core.ops.function.FnOnce
  pool_v1.pair_forest_terminal.validate_result.closure
  pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1 := {
  call_once :=
    pool_v1.pair_forest_terminal.validate_result.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1.call_once
}

/-- [aspis_statement::pool_v1::pair_forest_terminal::validate_result]:
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 537:0-551:1 -/
def pool_v1.pair_forest_terminal.validate_result
  (result : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1) :
  Result (core.result.Result Unit
    pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  := do
  let a := Array.repeat 32#usize 0#u8
  let b ←
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
      result.master_account a
  if b
  then
    ok (core.result.Result.Err
      pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonZeroBinding)
  else
    let a1 := Array.repeat 32#usize 0#u8
    let b1 ←
      core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
        result.selected_lane_account a1
    if b1
    then
      ok (core.result.Result.Err
        pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonZeroBinding)
    else
      let r ←
        pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1
          result.nullifier
      let r1 ←
        core.result.Result.map_err
          pool_v1.pair_forest_terminal.validate_result.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1
          r ()
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        if result.output_lane != val
        then
          ok (core.result.Result.Err
            pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.OutputLaneMismatch)
        else
          let r2 ←
            pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1
              result.verified_afterstate
          let r3 ←
            core.result.Result.map_err
              pool_v1.pair_forest_terminal.validate_result.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairForestTerminalFormatErrorV1
              r2 ()
          let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r3
          match cf1 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            ok (core.result.Result.Ok ())
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

#print axioms pool_v1.pair_forest_terminal.validate_result
end AspisR1TerminalDecoder

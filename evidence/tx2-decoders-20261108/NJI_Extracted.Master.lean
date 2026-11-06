import NJI_Extracted.Core
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
namespace NJI_Extracted

-- Opaque callees are explicit parameters, never axioms.
variable (NJI_call_0 : ∀ {T : Type} {U : Type} {N : Std.Usize} (cmpPartialEqInst : core.cmp.PartialEq
  T U),
(Slice T) → (Array U N) → Result Bool)

variable (NJI_call_1 : ∀ {Self : Type} {F : Type} {Clause0_Item : Type} (IteratorInst :
  core.iter.traits.iterator.Iterator Self Clause0_Item)
  (opsfunctionFnMutFTupleClause0_ItemBoolInst : core.ops.function.FnMut F
  Clause0_Item Bool),
Self → F → Result (Bool × Self))

variable (NJI_call_2 : ∀ {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
  core.ops.function.FnOnce O E F),
(core.result.Result T E) → O → Result (core.result.Result T F))

variable (NJI_call_3 : ∀ {T : Type} {F : Type} (opsfunctionFnMutFTupleMutATBoolInst :
  core.ops.function.FnMut F T Bool),
(core.slice.iter.IterMut T) → F → Result (Bool ×
    (core.slice.iter.IterMut T) × (core.slice.iter.IterMut T →
    core.slice.iter.IterMut T)))

variable (NJI_call_4 : ∀ {T : Type} {F : Type} (opsfunctionFnMutFTupleSharedATBoolInst :
  core.ops.function.FnMut F T Bool),
(core.slice.iter.Iter T) → F → Result (Bool × (core.slice.iter.Iter T)))

variable (NJI_call_5 : (Array Std.U8 32#usize) → Result (core.result.Result (Array
    aspis_core.field.M31 8#usize)
    aspis_statement.atomic_statement.AtomicStatementError))

variable (NJI_call_6 : (Slice Std.U8) → Result (core.result.Result
    aspis_statement.pool_v1.format.PoolIdentityV1
    aspis_statement.pool_v1.format.PoolV1FormatError))

variable (NJI_call_7 : aspis_statement.pool_v1.format.VerifierPolicyV1 → Result
    (core.result.Result Unit aspis_statement.pool_v1.format.PoolV1FormatError))

variable (NJI_call_8 : Result Std.U64)

/-- [aspis_statement::pool_v1::pair_forest_accounts::validate_master::{impl core::ops::function::FnMut<(&'_ u64,), bool> for aspis_statement::pool_v1::pair_forest_accounts::validate_master::closure#1}::call_mut]:
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs', lines 219:13-219:23
    Name pattern: [aspis_statement::pool_v1::pair_forest_accounts::validate_master::{core::ops::function::FnMut<aspis_statement::pool_v1::pair_forest_accounts::validate_master::closure#1, (&'_ u64), bool>}::call_mut] -/
@[rust_fun
  "aspis_statement::pool_v1::pair_forest_accounts::validate_master::{core::ops::function::FnMut<aspis_statement::pool_v1::pair_forest_accounts::validate_master::closure#1, (&'_ u64), bool>}::call_mut"]
def
  aspis_statement.pool_v1.pair_forest_accounts.validate_master.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU64Bool.call_mut
  (c : aspis_statement.pool_v1.pair_forest_accounts.validate_master.closure_1)
  (tupled_args : Std.U64) :
  Result (Bool ×
    aspis_statement.pool_v1.pair_forest_accounts.validate_master.closure_1)
  := do
  let i ← NJI_call_8
  ok (tupled_args > i, c)

/-- [aspis_statement::pool_v1::pair_forest_accounts::validate_master::{impl core::ops::function::FnOnce<(&'_ u64,), bool> for aspis_statement::pool_v1::pair_forest_accounts::validate_master::closure#1}::call_once]:
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs', lines 219:13-219:23
    Name pattern: [aspis_statement::pool_v1::pair_forest_accounts::validate_master::{core::ops::function::FnOnce<aspis_statement::pool_v1::pair_forest_accounts::validate_master::closure#1, (&'_ u64), bool>}::call_once] -/
@[rust_fun
  "aspis_statement::pool_v1::pair_forest_accounts::validate_master::{core::ops::function::FnOnce<aspis_statement::pool_v1::pair_forest_accounts::validate_master::closure#1, (&'_ u64), bool>}::call_once"]
def
  aspis_statement.pool_v1.pair_forest_accounts.validate_master.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedU64Bool.call_once
  (c : aspis_statement.pool_v1.pair_forest_accounts.validate_master.closure_1)
  (i : Std.U64) :
  Result Bool
  := do
  let (b, _) ←
    (aspis_statement.pool_v1.pair_forest_accounts.validate_master.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU64Bool.call_mut NJI_call_8)
      c i
  ok b

/-- Trait implementation: [aspis_statement::pool_v1::pair_forest_accounts::validate_master::{impl core::ops::function::FnOnce<(&'_ u64,), bool> for aspis_statement::pool_v1::pair_forest_accounts::validate_master::closure#1}]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs', lines 219:13-219:23
    Name pattern: [core::ops::function::FnOnce<aspis_statement::pool_v1::pair_forest_accounts::validate_master::closure#1, (&'_ u64), bool>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::pool_v1::pair_forest_accounts::validate_master::closure#1, (&'_ u64), bool>"]
def
  aspis_statement.pool_v1.pair_forest_accounts.validate_master.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedU64Bool
  : core.ops.function.FnOnce
  aspis_statement.pool_v1.pair_forest_accounts.validate_master.closure_1
  Std.U64 Bool := {
  call_once :=
    (aspis_statement.pool_v1.pair_forest_accounts.validate_master.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedU64Bool.call_once NJI_call_8)
}

/-- Trait implementation: [aspis_statement::pool_v1::pair_forest_accounts::validate_master::{impl core::ops::function::FnMut<(&'_ u64,), bool> for aspis_statement::pool_v1::pair_forest_accounts::validate_master::closure#1}]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs', lines 219:13-219:23
    Name pattern: [core::ops::function::FnMut<aspis_statement::pool_v1::pair_forest_accounts::validate_master::closure#1, (&'_ u64), bool>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::pool_v1::pair_forest_accounts::validate_master::closure#1, (&'_ u64), bool>"]
def
  aspis_statement.pool_v1.pair_forest_accounts.validate_master.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU64Bool
  : core.ops.function.FnMut
  aspis_statement.pool_v1.pair_forest_accounts.validate_master.closure_1
  Std.U64 Bool := {
  FnOnceInst :=
    (aspis_statement.pool_v1.pair_forest_accounts.validate_master.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedU64Bool NJI_call_8)
  call_mut :=
    (aspis_statement.pool_v1.pair_forest_accounts.validate_master.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU64Bool.call_mut NJI_call_8)
}

/-- [aspis_statement::pool_v1::pair_forest_accounts::validate_master::{impl core::ops::function::FnOnce<(aspis_statement::pool_v1::format::PoolV1FormatError,), aspis_statement::pool_v1::pair_forest_accounts::PoolV1PairForestAccountErrorV1> for aspis_statement::pool_v1::pair_forest_accounts::validate_master::closure}::call_once]:
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs', lines 215:17-215:20
    Name pattern: [aspis_statement::pool_v1::pair_forest_accounts::validate_master::{core::ops::function::FnOnce<aspis_statement::pool_v1::pair_forest_accounts::validate_master::closure, (aspis_statement::pool_v1::format::PoolV1FormatError), aspis_statement::pool_v1::pair_forest_accounts::PoolV1PairForestAccountErrorV1>}::call_once] -/
@[rust_fun
  "aspis_statement::pool_v1::pair_forest_accounts::validate_master::{core::ops::function::FnOnce<aspis_statement::pool_v1::pair_forest_accounts::validate_master::closure, (aspis_statement::pool_v1::format::PoolV1FormatError), aspis_statement::pool_v1::pair_forest_accounts::PoolV1PairForestAccountErrorV1>}::call_once"]
def
  aspis_statement.pool_v1.pair_forest_accounts.validate_master.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1FormatErrorPoolV1PairForestAccountErrorV1.call_once
  (c : aspis_statement.pool_v1.pair_forest_accounts.validate_master.closure)
  (tupled_args : aspis_statement.pool_v1.format.PoolV1FormatError) :
  Result
    aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
  := do
  ok
    aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.Policy

/-- Trait implementation: [aspis_statement::pool_v1::pair_forest_accounts::validate_master::{impl core::ops::function::FnOnce<(aspis_statement::pool_v1::format::PoolV1FormatError,), aspis_statement::pool_v1::pair_forest_accounts::PoolV1PairForestAccountErrorV1> for aspis_statement::pool_v1::pair_forest_accounts::validate_master::closure}]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs', lines 215:17-215:20
    Name pattern: [core::ops::function::FnOnce<aspis_statement::pool_v1::pair_forest_accounts::validate_master::closure, (aspis_statement::pool_v1::format::PoolV1FormatError), aspis_statement::pool_v1::pair_forest_accounts::PoolV1PairForestAccountErrorV1>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::pool_v1::pair_forest_accounts::validate_master::closure, (aspis_statement::pool_v1::format::PoolV1FormatError), aspis_statement::pool_v1::pair_forest_accounts::PoolV1PairForestAccountErrorV1>"]
def
  aspis_statement.pool_v1.pair_forest_accounts.validate_master.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1FormatErrorPoolV1PairForestAccountErrorV1
  : core.ops.function.FnOnce
  aspis_statement.pool_v1.pair_forest_accounts.validate_master.closure
  aspis_statement.pool_v1.format.PoolV1FormatError
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
  := {
  call_once :=
    aspis_statement.pool_v1.pair_forest_accounts.validate_master.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1FormatErrorPoolV1PairForestAccountErrorV1.call_once
}

/-- [aspis_statement::pool_v1::pair_forest_accounts::validate_master]:
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs', lines 204:0-206:47
    Name pattern: [aspis_statement::pool_v1::pair_forest_accounts::validate_master] -/
@[rust_fun "aspis_statement::pool_v1::pair_forest_accounts::validate_master"]
def aspis_statement.pool_v1.pair_forest_accounts.validate_master
  (master :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) :
  Result (core.result.Result Unit
    aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1)
  := do
  let a := Array.repeat 32#usize 0#u8
  let b ←
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
      master.identity.pool a
  if b
  then
    ok (core.result.Result.Err
      aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.ZeroRequiredBinding)
  else
    let a1 := Array.repeat 32#usize 0#u8
    let b1 ←
      core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
        master.identity.asset_mint a1
    if b1
    then
      ok (core.result.Result.Err
        aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.ZeroRequiredBinding)
    else
      let a2 := Array.repeat 32#usize 0#u8
      let b2 ←
        core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
          master.identity.token_program a2
      if b2
      then
        ok (core.result.Result.Err
          aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.ZeroRequiredBinding)
      else
        let a3 := Array.repeat 32#usize 0#u8
        let b3 ←
          core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
            master.identity.deployment_domain a3
        if b3
        then
          ok (core.result.Result.Err
            aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.ZeroRequiredBinding)
        else
          let r ←
            NJI_call_7
              master.verifier_policy
          let r1 ←
            NJI_call_2
              aspis_statement.pool_v1.pair_forest_accounts.validate_master.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1FormatErrorPoolV1PairForestAccountErrorV1
              r ()
          let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
          match cf with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let s ←
              lift (Array.to_slice master.last_checkpoint_lane_sequences)
            let i ← core.slice.Slice.iter s
            let (b4, _) ←
              NJI_call_4
                (aspis_statement.pool_v1.pair_forest_accounts.validate_master.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU64Bool NJI_call_8)
                i ()
            if b4
            then
              ok (core.result.Result.Err
                aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.InvalidMasterState)
            else
              if master.has_checkpoint
              then
                if master.next_checkpoint_sequence = 0#u64
                then
                  ok (core.result.Result.Err
                    aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.InvalidMasterState)
                else ok (core.result.Result.Ok ())
              else
                if master.next_checkpoint_sequence != 0#u64
                then
                  ok (core.result.Result.Err
                    aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.InvalidMasterState)
                else
                  let a4 := Array.repeat 8#usize 0#u64
                  let b5 ←
                    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU64
                      master.last_checkpoint_lane_sequences a4
                  if b5
                  then
                    ok (core.result.Result.Err
                      aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.InvalidMasterState)
                  else ok (core.result.Result.Ok ())
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Unit (core.convert.FromSame
              aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1)
              residual


end NJI_Extracted
#print axioms NJI_Extracted.aspis_statement.pool_v1.pair_forest_accounts.validate_master
#check NJI_Extracted.aspis_statement.pool_v1.pair_forest_accounts.validate_master

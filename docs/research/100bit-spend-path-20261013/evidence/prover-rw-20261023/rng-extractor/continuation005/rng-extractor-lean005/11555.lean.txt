import R1Z.ProverRwRngExtractor005Types
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace ProverRwRngExtractorsynthetic

/-- [core::num::niche_types::NonZeroI32Inner]
    Source: '/rustc/library/core/src/num/niche_types.rs', lines 20:8-20:55
    Name pattern: [core::num::niche_types::NonZeroI32Inner]
    Visibility: public -/
@[rust_type "core::num::niche_types::NonZeroI32Inner"]
structure core.num.niche_types.NonZeroI32Inner where
  _0 : { x : I32 // x.val ≠ 0 }

/-- [core::num::nonzero::NonZero]
    Source: '/rustc/library/core/src/num/nonzero.rs', lines 128:0-128:40
    Name pattern: [core::num::nonzero::NonZero]
    Visibility: public -/
@[rust_type "core::num::nonzero::NonZero"]
structure core.num.nonzero.NonZero (T : Type) (Clause0_NonZeroInner : Type)
  where
  _0 : Clause0_NonZeroInner

/-- [getrandom::error::Error]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/getrandom-0.3.4/src/error.rs', lines 36:0-36:16
    Name pattern: [getrandom::error::Error]
    Visibility: public -/
@[rust_type "getrandom::error::Error"]
structure getrandom.error.Error where
  _0 : core.num.nonzero.NonZero Std.I32 core.num.niche_types.NonZeroI32Inner

/-- [prover_rw_rng_extractor::EntropyError]
    Source: 'lib.rs', lines 3:0-3:65
    Visibility: public -/
inductive EntropyError where
| Os : getrandom.error.Error → EntropyError
| RepeatedZeroBlock : EntropyError

/-- [prover_rw_rng_extractor::selected::closure]
    Source: 'lib.rs', lines 10:19-10:25 -/
@[reducible]
def selected.closure := Unit


/-- [core::result::{core::result::Result<T, E>}::map_err]:
    Source: '/rustc/library/core/src/result.rs', lines 962:4-964:53
    Name pattern: [core::result::{core::result::Result<@T, @E>}::map_err]
    Visibility: public -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::map_err"]
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

/-- [prover_rw_rng_extractor::{impl core::convert::From<getrandom::error::Error> for prover_rw_rng_extractor::EntropyError}::from]:
    Source: 'lib.rs', lines 5:4-5:64
    Visibility: public -/
def EntropyError.Insts.CoreConvertFromError.from
  (value : getrandom.error.Error) : Result EntropyError := do
  ok (EntropyError.Os value)

/-- [prover_rw_rng_extractor::wrap]:
    Source: 'lib.rs', lines 7:0-7:82
    Visibility: public -/
def wrap (value : getrandom.error.Error) : Result EntropyError := do
  EntropyError.Insts.CoreConvertFromError.from value

/-- [prover_rw_rng_extractor::selected::{impl core::ops::function::FnOnce<(prover_rw_rng_extractor::EntropyError,), ()> for prover_rw_rng_extractor::selected::closure}::call_once]:
    Source: 'lib.rs', lines 10:19-10:25 -/
def
  selected.closure.Insts.CoreOpsFunctionFnOnceTupleEntropyErrorTuple.call_once
  (c : selected.closure) (tupled_args : EntropyError) : Result Unit := do
  ok ()

/-- Trait implementation: [prover_rw_rng_extractor::selected::{impl core::ops::function::FnOnce<(prover_rw_rng_extractor::EntropyError,), ()> for prover_rw_rng_extractor::selected::closure}]
    Source: 'lib.rs', lines 10:19-10:25 -/
@[reducible]
def selected.closure.Insts.CoreOpsFunctionFnOnceTupleEntropyErrorTuple :
  core.ops.function.FnOnce selected.closure EntropyError Unit := {
  call_once :=
    selected.closure.Insts.CoreOpsFunctionFnOnceTupleEntropyErrorTuple.call_once
}

/-- [prover_rw_rng_extractor::selected]:
    Source: 'lib.rs', lines 8:0-11:1
    Visibility: public -/
def selected
  (status : core.result.Result Unit getrandom.error.Error) :
  Result (core.result.Result Unit Unit)
  := do
  let status1 ←
    core.result.Result.map_err (BuiltinFnOnce getrandom.error.Error
      EntropyError) status (EntropyError.Insts.CoreConvertFromError.from)
  core.result.Result.map_err
    selected.closure.Insts.CoreOpsFunctionFnOnceTupleEntropyErrorTuple status1
    ()

/-- [prover_rw_rng_extractor::move_value]:
    Source: 'lib.rs', lines 12:0-12:83
    Visibility: public -/
def move_value (value : EntropyError) : Result EntropyError := do
  ok value

/-- [prover_rw_rng_extractor::copy_error]:
    Source: 'lib.rs', lines 13:0-15:1
    Visibility: public -/
def copy_error
  (value : getrandom.error.Error) :
  Result (getrandom.error.Error × getrandom.error.Error)
  := do
  ok (value, value)

/-- [prover_rw_rng_extractor::repeated]:
    Source: 'lib.rs', lines 16:0-16:69
    Visibility: public -/
def repeated : Result EntropyError := do
  ok EntropyError.RepeatedZeroBlock

end ProverRwRngExtractorsynthetic
namespace ProverRwRngExtractorselected64
/-- [core::result::{core::result::Result<T, E>}::map_err]:
    Source: '/rustc/library/core/src/result.rs', lines 962:4-964:53
    Name pattern: [core::result::{core::result::Result<@T, @E>}::map_err]
    Visibility: public -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::map_err"]
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

/-- [aspis_prover::state_only_entropy::{impl core::convert::From<getrandom::error::Error> for aspis_prover::state_only_entropy::StateOnlyAttemptEntropyError}::from]:
    Source: 'crates/aspis-prover/src/state_only_entropy.rs', lines 77:4-77:44
    Name pattern: [aspis_prover::state_only_entropy::{core::convert::From<aspis_prover::state_only_entropy::StateOnlyAttemptEntropyError, getrandom::error::Error>}::from]
    Visibility: public -/
@[rust_fun
  "aspis_prover::state_only_entropy::{core::convert::From<aspis_prover::state_only_entropy::StateOnlyAttemptEntropyError, getrandom::error::Error>}::from"]
def
  aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError.Insts.CoreConvertFromError.from
  (value : getrandom.error.Error) :
  Result aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError
  := do
  ok (aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError.Os value)

/-- Trait implementation: [aspis_prover::state_only_entropy::{impl core::convert::From<getrandom::error::Error> for aspis_prover::state_only_entropy::StateOnlyAttemptEntropyError}]
    Source: 'crates/aspis-prover/src/state_only_entropy.rs', lines 76:0-76:60
    Name pattern: [core::convert::From<aspis_prover::state_only_entropy::StateOnlyAttemptEntropyError, getrandom::error::Error>] -/
@[reducible, rust_trait_impl
  "core::convert::From<aspis_prover::state_only_entropy::StateOnlyAttemptEntropyError, getrandom::error::Error>"]
def
  aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError.Insts.CoreConvertFromError
  : core.convert.From
  aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError
  getrandom.error.Error := {
  «from» :=
    aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError.Insts.CoreConvertFromError.from
}

/-- [aspis_r1_cost_probe::RealR1_client::prove_for_proof_accounts::closure::{impl core::ops::function::FnOnce<(aspis_prover::state_only_entropy::StateOnlyAttemptEntropyError,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::RealR1_client::prove_for_proof_accounts::closure::closure<T0>}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/RealR1_client.rs', lines 28:83-28:101 -/
def
  RealR1_client.prove_for_proof_accounts.closure.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyAttemptEntropyErrorError.call_once
  {T0 : Type} (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst :
  core.ops.function.FnMut T0 Std.Usize (Array Std.U8 32#usize))
  (c : RealR1_client.prove_for_proof_accounts.closure.closure T0)
  (tupled_args : aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError)
  :
  Result verifier.Error
  := do
  ok verifier.Error.Entropy

/-- Trait implementation: [aspis_r1_cost_probe::RealR1_client::prove_for_proof_accounts::closure::{impl core::ops::function::FnOnce<(aspis_prover::state_only_entropy::StateOnlyAttemptEntropyError,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::RealR1_client::prove_for_proof_accounts::closure::closure<T0>}]
    Source: 'crates/aspis-r1-cost-probe/src/RealR1_client.rs', lines 28:83-28:101 -/
@[reducible]
def
  RealR1_client.prove_for_proof_accounts.closure.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyAttemptEntropyErrorError
  {T0 : Type} (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst :
  core.ops.function.FnMut T0 Std.Usize (Array Std.U8 32#usize)) :
  core.ops.function.FnOnce
  (RealR1_client.prove_for_proof_accounts.closure.closure T0)
  aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError verifier.Error
  := {
  call_once :=
    RealR1_client.prove_for_proof_accounts.closure.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyAttemptEntropyErrorError.call_once
    coreopsfunctionFnMutT0TupleUsizeArrayU832Inst
}

end ProverRwRngExtractorselected64

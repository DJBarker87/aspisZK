import S1ClaimsUnrolledTypesV1
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisS1ClaimsUnrolledSource

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

/-- [aspis_core::field::{impl core::clone::Clone for aspis_core::field::QM31}::clone]:
    Source: '/home/dombarker/project-offloads/s126-real-sdk-20261021/s1-claims-safe-extract-run4-20261025/core-workspace/crates/aspis-core/src/field.rs', lines 431:9-431:14
    Name pattern: [aspis_core::field::{core::clone::Clone<aspis_core::field::QM31>}::clone]
    Visibility: public -/
@[rust_fun
  "aspis_core::field::{core::clone::Clone<aspis_core::field::QM31>}::clone"]
def aspis_core.field.QM31.Insts.CoreCloneClone.clone
  (self : aspis_core.field.QM31) : Result aspis_core.field.QM31 := do
  ok self

/-- Trait implementation: [aspis_core::field::{impl core::clone::Clone for aspis_core::field::QM31}]
    Source: '/home/dombarker/project-offloads/s126-real-sdk-20261021/s1-claims-safe-extract-run4-20261025/core-workspace/crates/aspis-core/src/field.rs', lines 431:9-431:14
    Name pattern: [core::clone::Clone<aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl "core::clone::Clone<aspis_core::field::QM31>"]
def aspis_core.field.QM31.Insts.CoreCloneClone : core.clone.Clone
  aspis_core.field.QM31 := {
  clone := aspis_core.field.QM31.Insts.CoreCloneClone.clone
}

/-- Trait implementation: [aspis_core::field::{impl core::marker::Copy for aspis_core::field::QM31}]
    Source: '/home/dombarker/project-offloads/s126-real-sdk-20261021/s1-claims-safe-extract-run4-20261025/core-workspace/crates/aspis-core/src/field.rs', lines 431:16-431:20
    Name pattern: [core::marker::Copy<aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl "core::marker::Copy<aspis_core::field::QM31>"]
def aspis_core.field.QM31.Insts.CoreMarkerCopy : core.marker.Copy
  aspis_core.field.QM31 := {
  cloneInst := aspis_core.field.QM31.Insts.CoreCloneClone
}

/-- [aspis_core::field::{aspis_core::field::QM31}::ZERO]
    Source: '/home/dombarker/project-offloads/s126-real-sdk-20261021/s1-claims-safe-extract-run4-20261025/core-workspace/crates/aspis-core/src/field.rs', lines 869:4-869:24
    Name pattern: [aspis_core::field::{aspis_core::field::QM31}::ZERO]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::field::{aspis_core::field::QM31}::ZERO"]
def aspis_core.field.QM31.ZERO : aspis_core.field.QM31 :=
  { c0 := { a := 0#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }

/-- [aspis_core::r0::heap::filled::{impl core::ops::function::FnOnce<(alloc::collections::TryReserveError,), aspis_core::r0::Error> for aspis_core::r0::heap::filled::closure<T>}::call_once]:
    Source: '/home/dombarker/project-offloads/s126-real-sdk-20261021/s1-claims-safe-extract-run4-20261025/core-workspace/crates/aspis-core/src/r0/heap.rs', lines 7:37-7:40
    Name pattern: [aspis_core::r0::heap::filled::{core::ops::function::FnOnce<aspis_core::r0::heap::filled::closure<@T>, (alloc::collections::TryReserveError), aspis_core::r0::Error>}::call_once] -/
@[rust_fun
  "aspis_core::r0::heap::filled::{core::ops::function::FnOnce<aspis_core::r0::heap::filled::closure<@T>, (alloc::collections::TryReserveError), aspis_core::r0::Error>}::call_once"]
def
  aspis_core.r0.heap.filled.closure.Insts.CoreOpsFunctionFnOnceTupleTryReserveErrorError.call_once
  {T : Type} (coremarkerCopyInst : core.marker.Copy T)
  (c : aspis_core.r0.heap.filled.closure T)
  (tupled_args : alloc.collections.TryReserveError) :
  Result aspis_core.r0.Error
  := do
  ok aspis_core.r0.Error.Allocation

/-- Trait implementation: [aspis_core::r0::heap::filled::{impl core::ops::function::FnOnce<(alloc::collections::TryReserveError,), aspis_core::r0::Error> for aspis_core::r0::heap::filled::closure<T>}]
    Source: '/home/dombarker/project-offloads/s126-real-sdk-20261021/s1-claims-safe-extract-run4-20261025/core-workspace/crates/aspis-core/src/r0/heap.rs', lines 7:37-7:40
    Name pattern: [core::ops::function::FnOnce<aspis_core::r0::heap::filled::closure<@T>, (alloc::collections::TryReserveError), aspis_core::r0::Error>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::r0::heap::filled::closure<@T>, (alloc::collections::TryReserveError), aspis_core::r0::Error>"]
def
  aspis_core.r0.heap.filled.closure.Insts.CoreOpsFunctionFnOnceTupleTryReserveErrorError
  {T : Type} (coremarkerCopyInst : core.marker.Copy T) :
  core.ops.function.FnOnce (aspis_core.r0.heap.filled.closure T)
  alloc.collections.TryReserveError aspis_core.r0.Error := {
  call_once :=
    aspis_core.r0.heap.filled.closure.Insts.CoreOpsFunctionFnOnceTupleTryReserveErrorError.call_once
    coremarkerCopyInst
}

/-- [aspis_r1_cost_probe::r1_wire::{aspis_r1_cost_probe::r1_wire::Prefix<'a>}::record]:
    Source: 'src/r1_wire.rs', lines 338:4-343:5
    Visibility: public -/
def r1_wire.Prefix.record
  (self : r1_wire.Prefix) (row : Std.U8) :
  Result (core.result.Result (Slice Std.U8) r1_wire.Error)
  := do
  if row >= 27#u8
  then ok (core.result.Result.Err r1_wire.Error.InvalidRow)
  else
    let i ← lift (UScalar.cast .Usize row)
    let s ← Array.index_usize self.records i
    ok (core.result.Result.Ok s)

/-- [aspis_r1_cost_probe::r1_wire::{aspis_r1_cost_probe::r1_wire::Prefix<'a>}::validated_record]:
    Source: 'src/r1_wire.rs', lines 348:4-353:5 -/
def r1_wire.Prefix.validated_record
  (self : r1_wire.Prefix) (row : Std.U8) :
  Result (core.result.Result r1_wire.ValidatedRecord r1_wire.Error)
  := do
  let r ← r1_wire.Prefix.record self row
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    ok (core.result.Result.Ok { row, framed := val })
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      r1_wire.ValidatedRecord (core.convert.FromSame r1_wire.Error) residual

/-- [aspis_r1_cost_probe::candidate_claims::claims::{impl core::ops::function::FnOnce<(alloc::boxed::Box<[[aspis_core::field::QM31; 29usize]]>,), aspis_r1_cost_probe::r1_wire::Error> for aspis_r1_cost_probe::candidate_claims::claims::closure#1}::call_once]:
    Source: 'src/candidate_claims.rs', lines 12:17-12:38 -/
def
  candidate_claims.claims.closure_1.Insts.CoreOpsFunctionFnOnceTupleBoxSliceArrayQM3129Error.call_once
  (c : candidate_claims.claims.closure_1)
  (tupled_args : Slice (Array aspis_core.field.QM31 29#usize)) :
  Result r1_wire.Error
  := do
  ok r1_wire.Error.Allocation

/-- Trait implementation: [aspis_r1_cost_probe::candidate_claims::claims::{impl core::ops::function::FnOnce<(alloc::boxed::Box<[[aspis_core::field::QM31; 29usize]]>,), aspis_r1_cost_probe::r1_wire::Error> for aspis_r1_cost_probe::candidate_claims::claims::closure#1}]
    Source: 'src/candidate_claims.rs', lines 12:17-12:38 -/
@[reducible]
def
  candidate_claims.claims.closure_1.Insts.CoreOpsFunctionFnOnceTupleBoxSliceArrayQM3129Error
  : core.ops.function.FnOnce candidate_claims.claims.closure_1 (Slice (Array
  aspis_core.field.QM31 29#usize)) r1_wire.Error := {
  call_once :=
    candidate_claims.claims.closure_1.Insts.CoreOpsFunctionFnOnceTupleBoxSliceArrayQM3129Error.call_once
}

/-- [aspis_r1_cost_probe::candidate_claims::claims::{impl core::ops::function::FnOnce<(aspis_core::r0::Error,), aspis_r1_cost_probe::r1_wire::Error> for aspis_r1_cost_probe::candidate_claims::claims::closure}::call_once]:
    Source: 'src/candidate_claims.rs', lines 8:17-8:38 -/
def
  candidate_claims.claims.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
  (c : candidate_claims.claims.closure) (tupled_args : aspis_core.r0.Error) :
  Result r1_wire.Error
  := do
  ok r1_wire.Error.Allocation

/-- Trait implementation: [aspis_r1_cost_probe::candidate_claims::claims::{impl core::ops::function::FnOnce<(aspis_core::r0::Error,), aspis_r1_cost_probe::r1_wire::Error> for aspis_r1_cost_probe::candidate_claims::claims::closure}]
    Source: 'src/candidate_claims.rs', lines 8:17-8:38 -/
@[reducible]
def candidate_claims.claims.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
  : core.ops.function.FnOnce candidate_claims.claims.closure
  aspis_core.r0.Error r1_wire.Error := {
  call_once :=
    candidate_claims.claims.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
}


end AspisS1ClaimsUnrolledSource

#print axioms AspisS1ClaimsUnrolledSource.core.result.Result.map_err

#print axioms AspisS1ClaimsUnrolledSource.aspis_core.field.QM31.Insts.CoreCloneClone.clone

#print axioms AspisS1ClaimsUnrolledSource.aspis_core.field.QM31.ZERO

#print axioms AspisS1ClaimsUnrolledSource.r1_wire.Prefix.record

#print axioms AspisS1ClaimsUnrolledSource.r1_wire.Prefix.validated_record

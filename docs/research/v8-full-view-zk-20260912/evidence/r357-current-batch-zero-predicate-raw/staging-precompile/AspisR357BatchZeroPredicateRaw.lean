import Aeneas.Std
import AspisR249R110Raw
import AspisR278PrivateInverseRaw

open Aeneas Aeneas.Std Result
open AspisR249R110Raw AspisR278PrivateInverseRaw

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

noncomputable section
namespace AspisR357BatchZeroPredicateRaw

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch::closure]
    Source: '../r110_norm.rs', lines 62:61-62:75 -/
@[reducible]
def circle_norm.joined_inverse.line_norm.r110_norm.batch.closure := Unit

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{impl core::cmp::PartialEq<aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::B> for aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::B}::eq]:
    Source: '../r110_norm.rs', lines 5:20-5:29
    Visibility: public -/
def circle_norm.joined_inverse.line_norm.r110_norm.B.Insts.CoreCmpPartialEqB.eq
  (self : circle_norm.joined_inverse.line_norm.r110_norm.B)
  (other : circle_norm.joined_inverse.line_norm.r110_norm.B) :
  Result Bool
  := do
  ok (self = other)

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch::{impl core::ops::function::FnMut<(&'_ aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::B,), bool> for aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch::closure}::call_mut]:
    Source: '../r110_norm.rs', lines 62:61-62:75 -/
def
  circle_norm.joined_inverse.line_norm.r110_norm.batch.closure.Insts.CoreOpsFunctionFnMutTupleSharedBBool.call_mut
  (c : circle_norm.joined_inverse.line_norm.r110_norm.batch.closure)
  (tupled_args : circle_norm.joined_inverse.line_norm.r110_norm.B) :
  Result (Bool × circle_norm.joined_inverse.line_norm.r110_norm.batch.closure)
  := do
  let b ←
    circle_norm.joined_inverse.line_norm.r110_norm.B.Insts.CoreCmpPartialEqB.eq
      tupled_args circle_norm.joined_inverse.line_norm.r110_norm.B.ZERO
  ok (b, c)

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch::{impl core::ops::function::FnOnce<(&'_ aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::B,), bool> for aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch::closure}::call_once]:
    Source: '../r110_norm.rs', lines 62:61-62:75 -/
def
  circle_norm.joined_inverse.line_norm.r110_norm.batch.closure.Insts.CoreOpsFunctionFnOnceTupleSharedBBool.call_once
  (c : circle_norm.joined_inverse.line_norm.r110_norm.batch.closure)
  (b : circle_norm.joined_inverse.line_norm.r110_norm.B) :
  Result Bool
  := do
  let (b1, _) ←
    circle_norm.joined_inverse.line_norm.r110_norm.batch.closure.Insts.CoreOpsFunctionFnMutTupleSharedBBool.call_mut
      c b
  ok b1

/-- Trait implementation: [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch::{impl core::ops::function::FnOnce<(&'_ aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::B,), bool> for aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch::closure}]
    Source: '../r110_norm.rs', lines 62:61-62:75 -/
@[reducible]
def
  circle_norm.joined_inverse.line_norm.r110_norm.batch.closure.Insts.CoreOpsFunctionFnOnceTupleSharedBBool
  : core.ops.function.FnOnce
  circle_norm.joined_inverse.line_norm.r110_norm.batch.closure
  circle_norm.joined_inverse.line_norm.r110_norm.B Bool := {
  call_once :=
    circle_norm.joined_inverse.line_norm.r110_norm.batch.closure.Insts.CoreOpsFunctionFnOnceTupleSharedBBool.call_once
}

/-- Trait implementation: [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch::{impl core::ops::function::FnMut<(&'_ aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::B,), bool> for aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch::closure}]
    Source: '../r110_norm.rs', lines 62:61-62:75 -/
@[reducible]
def
  circle_norm.joined_inverse.line_norm.r110_norm.batch.closure.Insts.CoreOpsFunctionFnMutTupleSharedBBool
  : core.ops.function.FnMut
  circle_norm.joined_inverse.line_norm.r110_norm.batch.closure
  circle_norm.joined_inverse.line_norm.r110_norm.B Bool := {
  FnOnceInst :=
    circle_norm.joined_inverse.line_norm.r110_norm.batch.closure.Insts.CoreOpsFunctionFnOnceTupleSharedBBool
  call_mut :=
    circle_norm.joined_inverse.line_norm.r110_norm.batch.closure.Insts.CoreOpsFunctionFnMutTupleSharedBBool.call_mut
}

#print axioms circle_norm.joined_inverse.line_norm.r110_norm.batch.closure
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.B.Insts.CoreCmpPartialEqB.eq
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.batch.closure.Insts.CoreOpsFunctionFnMutTupleSharedBBool.call_mut
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.batch.closure.Insts.CoreOpsFunctionFnOnceTupleSharedBBool.call_once
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.batch.closure.Insts.CoreOpsFunctionFnOnceTupleSharedBBool
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.batch.closure.Insts.CoreOpsFunctionFnMutTupleSharedBBool

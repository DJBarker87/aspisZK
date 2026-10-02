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

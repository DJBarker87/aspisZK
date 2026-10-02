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

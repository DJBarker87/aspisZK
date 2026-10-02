/-- [aspis_core::field::{aspis_core::field::M31}::reduce_u62]:
    Source: '/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a/crates/aspis-core/src/field.rs', lines 103:4-103:40
    Name pattern: [aspis_core::field::{aspis_core::field::M31}::reduce_u62]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::M31}::reduce_u62"]
def aspis_core.field.M31.reduce_u62
  (value : Std.U64) : Result aspis_core.field.M31 := do
  let i ← aspis_core.field.reduce_u64 value
  ok i

import R1Z.ProverRwP6BodyGammaPort
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP7TraceCloneSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
/-- Trait implementation: [aspis_core::field::{impl core::clone::Clone for aspis_core::field::M31}]
    Source: '/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/crates/aspis-core/src/field.rs', lines 22:9-22:14
    Name pattern: [core::clone::Clone<aspis_core::field::M31>] -/
@[reducible, rust_trait_impl "core::clone::Clone<aspis_core::field::M31>"]
def aspis_core.field.M31.Insts.CoreCloneClone : core.clone.Clone
  aspis_core.field.M31 := {
  clone := aspis_core.field.M31.Insts.CoreCloneClone.clone
}

/-- [aspis_statement::state_only_trace::{impl core::clone::Clone for aspis_statement::state_only_trace::StateOnlyTraceFoundation}::clone]:
    Source: '/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/crates/aspis-statement/src/state_only_trace.rs', lines 74:9-74:14
    Name pattern: [aspis_statement::state_only_trace::{core::clone::Clone<aspis_statement::state_only_trace::StateOnlyTraceFoundation>}::clone]
    Visibility: public -/
@[rust_fun
  "aspis_statement::state_only_trace::{core::clone::Clone<aspis_statement::state_only_trace::StateOnlyTraceFoundation>}::clone"]
def
  aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone
  (self : aspis_statement.state_only_trace.StateOnlyTraceFoundation) :
  Result aspis_statement.state_only_trace.StateOnlyTraceFoundation
  := do
  let a ←
    core.array.CloneArray.clone (core.clone.CloneallocvecVec
      aspis_core.field.M31.Insts.CoreCloneClone) self.c1
  ok { c1 := a }

/-- [prover_rw_success_p7::trace_clone]:
    Source: 'lib.rs', lines 21:0-21:155
    Visibility: public -/
def trace_clone
  (x : aspis_statement.state_only_trace.StateOnlyTraceFoundation) :
  Result aspis_statement.state_only_trace.StateOnlyTraceFoundation
  := do
  aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone
    x

end R1Z.ProverRwP7TraceCloneSource

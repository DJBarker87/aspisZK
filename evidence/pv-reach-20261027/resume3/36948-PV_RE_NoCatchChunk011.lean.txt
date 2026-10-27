import R1Z.PV_RE_NoCatchGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix022
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_sumcheck.interpolate`.
Recursive calls remain the original extracted calls. -/
def continueAfter (values : Array aspis_core.field.QM31 28#usize) (out : Payload (aspis_core.field.QM31.ZERO)) : Result (Array aspis_core.field.QM31 28#usize) := do
  let q := out
  let out := Array.repeat 28#usize q
  host_sumcheck.interpolate_loop values out 0#usize


end R1Z.PV_RE_NoCatchSuffix022
pv_no_catch_binds ProverRwFull.host_sumcheck.interpolate
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix022.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix023
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_sumcheck.interpolation_basis`.
Recursive calls remain the original extracted calls. -/
def continueAfter (i : Std.Usize) (out : Payload (aspis_core.field.M31.ZERO)) : Result ((Array aspis_core.field.M31 28#usize) × aspis_core.field.M31) := do
  let m := out
  let basis := Array.repeat 28#usize m
  let m1 ← aspis_core.field.M31.ONE
  let basis1 ← Array.update basis 0#usize m1
  host_sumcheck.interpolation_basis_steps basis1 m1 0#usize i 0#usize


end R1Z.PV_RE_NoCatchSuffix023
pv_no_catch_binds ProverRwFull.host_sumcheck.interpolation_basis
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix023.continueAfter

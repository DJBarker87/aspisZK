import R1Z.PV_RE_NoCatchGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix012
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_commitment.secure_coefficients`.
Recursive calls remain the original extracted calls. -/
def continueAfter (coefficients : Array aspis_core.field.wide_exact.WideExact 1024#usize) (out : Payload (aspis_core.field.QM31.ZERO)) : Result (Array aspis_core.field.QM31 1024#usize) := do
  let q := out
  let out := Array.repeat 1024#usize q
  host_commitment.secure_coefficients_loop coefficients out 0#usize


end R1Z.PV_RE_NoCatchSuffix012
pv_no_catch_binds ProverRwFull.host_commitment.secure_coefficients
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix012.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix013
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.boolean_point`.
Recursive calls remain the original extracted calls. -/
def continueAfter (row : Std.Usize) (out : Payload (aspis_core.field.QM31.ZERO)) : Result (Array aspis_core.field.QM31 10#usize) := do
  let q := out
  let point := Array.repeat 10#usize q
  host_semantic.boolean_point_loop q row point 0#usize


end R1Z.PV_RE_NoCatchSuffix013
pv_no_catch_binds ProverRwFull.host_semantic.boolean_point
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix013.continueAfter

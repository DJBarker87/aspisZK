import R1Z.PV_RE_NoCatchGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix016
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.extra`.
Recursive calls remain the original extracted calls. -/
def continueAfter (coefficients : Array aspis_core.field.QM31 1024#usize) (a : aspis_core.field.QM31) (b : aspis_core.field.QM31) (out : Payload (aspis_core.field.QM31.ZERO)) : Result aspis_core.field.QM31 := do
  let sum := out
  host_semantic.extra_loop0 sum coefficients a b sum 0#usize


end R1Z.PV_RE_NoCatchSuffix016
pv_no_catch_binds ProverRwFull.host_semantic.extra
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix016.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix017
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.extra_claims`.
Recursive calls remain the original extracted calls. -/
def continueAfter (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize) (variant : transport.Variant) (a : aspis_core.field.QM31) (b : aspis_core.field.QM31) (out : Payload (aspis_core.field.QM31.ZERO)) : Result (Array aspis_core.field.QM31 29#usize) := do
  let q := out
  let extras := Array.repeat 29#usize q
  host_semantic.extra_claims_loop columns variant a b extras 0#usize


end R1Z.PV_RE_NoCatchSuffix017
pv_no_catch_binds ProverRwFull.host_semantic.extra_claims
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix017.continueAfter

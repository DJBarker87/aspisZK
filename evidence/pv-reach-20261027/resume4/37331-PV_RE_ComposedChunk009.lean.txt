import R1Z.PV_RE_ComposedContextsGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix009
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_commitment.base_coefficients`.
Recursive calls remain the original extracted calls. -/
def continueAfter (coefficients : Array aspis_core.field.wide_exact.WideExact 1024#usize) (out : Payload (aspis_core.field.M31.ZERO)) : Result (Array aspis_core.field.M31 1024#usize) := do
  let m := out
  let out := Array.repeat 1024#usize m
  host_commitment.base_coefficients_loop coefficients out 0#usize


end R1Z.PV_RE_ComposedSuffix009
pv_composed_source_contexts ProverRwFull.host_commitment.base_coefficients
pv_composed_source_contexts R1Z.PV_RE_ComposedSuffix009.continueAfter

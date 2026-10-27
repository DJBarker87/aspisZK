import R1Z.PV_RE_DictSuffix008
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix009
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_commitment.base_coefficients`.
Recursive calls remain the original extracted calls. -/
def continueAfter (coefficients : Array aspis_core.field.wide_exact.WideExact 1024#usize) (out : Payload (aspis_core.field.M31.ZERO)) : Result (Array aspis_core.field.M31 1024#usize) := do
  let m := out
  let out := Array.repeat 1024#usize m
  host_commitment.base_coefficients_loop coefficients out 0#usize


end R1Z.PV_RE_DictSuffix009
pv_dict_congr ProverRwFull.host_commitment.base_coefficients
pv_dict_congr R1Z.PV_RE_DictSuffix009.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.host_commitment.base_coefficients
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix009.continueAfter

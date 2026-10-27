import R1Z.PV_RE_DictSuffix016
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix017
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.extra_claims`.
Recursive calls remain the original extracted calls. -/
def continueAfter (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize) (variant : transport.Variant) (a : aspis_core.field.QM31) (b : aspis_core.field.QM31) (out : Payload (aspis_core.field.QM31.ZERO)) : Result (Array aspis_core.field.QM31 29#usize) := do
  let q := out
  let extras := Array.repeat 29#usize q
  host_semantic.extra_claims_loop columns variant a b extras 0#usize


end R1Z.PV_RE_DictSuffix017
pv_dict_congr ProverRwFull.host_semantic.extra_claims
pv_dict_congr R1Z.PV_RE_DictSuffix017.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.host_semantic.extra_claims
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix017.continueAfter

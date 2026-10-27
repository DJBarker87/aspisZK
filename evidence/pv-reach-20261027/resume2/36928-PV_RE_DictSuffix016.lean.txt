import R1Z.PV_RE_DictSuffix015
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix016
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.extra`.
Recursive calls remain the original extracted calls. -/
def continueAfter (coefficients : Array aspis_core.field.QM31 1024#usize) (a : aspis_core.field.QM31) (b : aspis_core.field.QM31) (out : Payload (aspis_core.field.QM31.ZERO)) : Result aspis_core.field.QM31 := do
  let sum := out
  host_semantic.extra_loop0 sum coefficients a b sum 0#usize


end R1Z.PV_RE_DictSuffix016
pv_dict_congr ProverRwFull.host_semantic.extra
pv_dict_congr R1Z.PV_RE_DictSuffix016.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.host_semantic.extra
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix016.continueAfter

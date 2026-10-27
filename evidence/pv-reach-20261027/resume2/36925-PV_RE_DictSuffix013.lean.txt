import R1Z.PV_RE_DictSuffix012
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix013
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.boolean_point`.
Recursive calls remain the original extracted calls. -/
def continueAfter (row : Std.Usize) (out : Payload (aspis_core.field.QM31.ZERO)) : Result (Array aspis_core.field.QM31 10#usize) := do
  let q := out
  let point := Array.repeat 10#usize q
  host_semantic.boolean_point_loop q row point 0#usize


end R1Z.PV_RE_DictSuffix013
pv_dict_congr ProverRwFull.host_semantic.boolean_point
pv_dict_congr R1Z.PV_RE_DictSuffix013.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.host_semantic.boolean_point
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix013.continueAfter

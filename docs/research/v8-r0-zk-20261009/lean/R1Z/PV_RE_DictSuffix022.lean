import R1Z.PV_RE_DictSuffix021
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix022
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_sumcheck.interpolate`.
Recursive calls remain the original extracted calls. -/
def continueAfter (values : Array aspis_core.field.QM31 28#usize) (out : Payload (aspis_core.field.QM31.ZERO)) : Result (Array aspis_core.field.QM31 28#usize) := do
  let q := out
  let out := Array.repeat 28#usize q
  host_sumcheck.interpolate_loop values out 0#usize


end R1Z.PV_RE_DictSuffix022
pv_dict_congr ProverRwFull.host_sumcheck.interpolate
pv_dict_congr R1Z.PV_RE_DictSuffix022.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.host_sumcheck.interpolate
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix022.continueAfter

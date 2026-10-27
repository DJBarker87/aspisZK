import R1Z.PV_RE_DictSuffix030
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix031
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.inactive_sum_m31`.
Recursive calls remain the original extracted calls. -/
def continueAfter (values : Slice aspis_core.field.M31) (masks : Array Std.U16 64#usize) (out : Payload (aspis_core.field.M31.ZERO)) : Result aspis_core.field.M31 := do
  let sum := out
  prover.inactive_sum_m31_loop values masks sum 0#usize


end R1Z.PV_RE_DictSuffix031
pv_dict_congr ProverRwFull.prover.inactive_sum_m31
pv_dict_congr R1Z.PV_RE_DictSuffix031.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.prover.inactive_sum_m31
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix031.continueAfter

import R1Z.PV_RE_DictSuffix017
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix018
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.initial_mask_sum`.
Recursive calls remain the original extracted calls. -/
def continueAfter (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize) (out : Payload (aspis_core.field.QM31.ZERO)) : Result aspis_core.field.QM31 := do
  let sum := out
  host_semantic.initial_mask_sum_loop columns sum 0#usize


end R1Z.PV_RE_DictSuffix018
pv_dict_congr ProverRwFull.host_semantic.initial_mask_sum
pv_dict_congr R1Z.PV_RE_DictSuffix018.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.host_semantic.initial_mask_sum
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix018.continueAfter

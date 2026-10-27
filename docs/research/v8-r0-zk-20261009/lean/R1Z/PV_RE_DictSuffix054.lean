import R1Z.PV_RE_DictSuffix053
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix054
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.add_d_tail`.
Recursive calls remain the original extracted calls. -/
def continueAfter (mask_sum : aspis_core.field.QM31) (dc : Array aspis_core.field.QM31 1024#usize) (out : Payload (host_semantic.d_tail_side dc 0#usize)) : Result aspis_core.field.QM31 := do
  let q := out
  let first ← aspis_core.field.QM31.mul_m31 q 512#u32
  let mask_sum1 ← aspis_core.field.QM31.add mask_sum first
  let q1 ← host_semantic.d_tail_side dc 28#usize
  let second ← aspis_core.field.QM31.mul_m31 q1 512#u32
  aspis_core.field.QM31.add mask_sum1 second


end R1Z.PV_RE_DictSuffix054
pv_dict_congr ProverRwFull.host_semantic.add_d_tail
pv_dict_congr R1Z.PV_RE_DictSuffix054.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.host_semantic.add_d_tail
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix054.continueAfter

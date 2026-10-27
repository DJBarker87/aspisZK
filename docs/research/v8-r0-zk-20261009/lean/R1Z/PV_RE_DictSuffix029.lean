import R1Z.PV_RE_DictSuffix028
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix029
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.fixed_k_column`.
Recursive calls remain the original extracted calls. -/
def continueAfter (values : Slice aspis_core.field.QM31) (out : Payload (aspis_core.field.QM31.ZERO)) : Result (Array aspis_core.field.QM31 1024#usize) := do
  let q := out
  let out := Array.repeat 1024#usize q
  prover.fixed_k_column_loop values out 0#usize


end R1Z.PV_RE_DictSuffix029
pv_dict_congr ProverRwFull.prover.fixed_k_column
pv_dict_congr R1Z.PV_RE_DictSuffix029.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.prover.fixed_k_column
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix029.continueAfter

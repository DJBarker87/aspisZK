import R1Z.PV_RE_DictSuffix033
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix034
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.opening_row`.
Recursive calls remain the original extracted calls. -/
def continueAfter (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize)) (gp : Array aspis_core.field.wide_exact.WideExact 29#usize) (row : Std.Usize) (out : Payload (aspis_core.field.wide_exact.WideExact.ZERO)) : Result aspis_core.field.wide_exact.WideExact := do
  let value := out
  prover.opening_row_loop coefficients gp row value 0#usize


end R1Z.PV_RE_DictSuffix034
pv_dict_congr ProverRwFull.prover.opening_row
pv_dict_congr R1Z.PV_RE_DictSuffix034.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.prover.opening_row
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix034.continueAfter

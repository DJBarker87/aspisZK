import R1Z.PV_RE_DictSuffix023
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix024
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_sumcheck.merge_evaluations`.
Recursive calls remain the original extracted calls. -/
def continueAfter (evaluations : Slice (core.result.Result aspis_core.field.QM31
  r1_wire.Error)) (assignments : Std.Usize) (out : Payload (aspis_core.field.QM31.ZERO)) : Result (core.result.Result (Array aspis_core.field.QM31 28#usize)
    r1_wire.Error) := do
  let q := out
  let values := Array.repeat 28#usize q
  let count := Slice.len evaluations
  let (values1, pending_return) ←
    host_sumcheck.merge_evaluations_loop evaluations assignments values count
      0#usize
  match pending_return with
  | none => ok (core.result.Result.Ok values1)
  | some r => ok r


end R1Z.PV_RE_DictSuffix024
pv_dict_congr ProverRwFull.host_sumcheck.merge_evaluations
pv_dict_congr R1Z.PV_RE_DictSuffix024.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.host_sumcheck.merge_evaluations
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix024.continueAfter

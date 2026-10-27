import R1Z.PV_RE_DictSuffix050
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix051
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_commitment.validate_commitment_lanes`.
Recursive calls remain the original extracted calls. -/
def continueAfter (messages : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize)) (lanes : Slice Std.Usize) (out : Payload (host_commitment.validate_commitment_lanes_loop messages lanes 0#usize)) : Result (core.result.Result Unit aspis_core.r0.Error) := do
  let pending_return := out
  match pending_return with
  | none => ok (core.result.Result.Ok ())
  | some r => ok r


end R1Z.PV_RE_DictSuffix051
pv_dict_congr ProverRwFull.host_commitment.validate_commitment_lanes
pv_dict_congr R1Z.PV_RE_DictSuffix051.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.host_commitment.validate_commitment_lanes
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix051.continueAfter

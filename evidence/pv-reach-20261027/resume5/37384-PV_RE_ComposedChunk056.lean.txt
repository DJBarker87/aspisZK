import R1Z.PV_RE_ComposedContextsGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix056
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.check_secure_column`.
Recursive calls remain the original extracted calls. -/
def continueAfter (column : Array aspis_core.field.QM31 1024#usize) (out : Payload (host_semantic.check_secure_column_loop column 0#usize)) : Result (core.result.Result Unit r1_wire.Error) := do
  let pending_return := out
  match pending_return with
  | none => ok (core.result.Result.Ok ())
  | some r => ok r


end R1Z.PV_RE_ComposedSuffix056
pv_composed_source_contexts ProverRwFull.host_semantic.check_secure_column
pv_composed_source_contexts R1Z.PV_RE_ComposedSuffix056.continueAfter

import R1Z.PV_RE_ComposedContextsGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix015
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.claims_at_point`.
Recursive calls remain the original extracted calls. -/
def continueAfter (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize) (point : Array aspis_core.field.QM31 10#usize) (out : Payload (aspis_core.field.QM31.ZERO)) : Result (core.result.Result (Array aspis_core.field.QM31 29#usize)
    r1_wire.Error) := do
  let q := out
  let claims := Array.repeat 29#usize q
  let (claims1, pending_return) ←
    host_semantic.claims_at_point_loop columns point claims 0#usize
  match pending_return with
  | none => ok (core.result.Result.Ok claims1)
  | some r => ok r


end R1Z.PV_RE_ComposedSuffix015
pv_composed_source_contexts ProverRwFull.host_semantic.claims_at_point
pv_composed_source_contexts R1Z.PV_RE_ComposedSuffix015.continueAfter

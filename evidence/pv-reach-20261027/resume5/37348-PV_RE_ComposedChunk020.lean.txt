import R1Z.PV_RE_ComposedContextsGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix020
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.lift`.
Recursive calls remain the original extracted calls. -/
def continueAfter (x : aspis_core.field.M31) (out : Payload (aspis_core.field.CM31.from_m31 x)) : Result aspis_core.field.QM31 := do
  let c := out
  aspis_core.field.QM31.from_cm31 c


end R1Z.PV_RE_ComposedSuffix020
pv_composed_source_contexts ProverRwFull.host_semantic.lift
pv_composed_source_contexts R1Z.PV_RE_ComposedSuffix020.continueAfter

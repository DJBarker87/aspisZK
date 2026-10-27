import R1Z.PV_RE_ComposedContextsGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix030
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.inactive_sum_k`.
Recursive calls remain the original extracted calls. -/
def continueAfter (values : Slice aspis_core.field.QM31) (masks : Array Std.U16 64#usize) (out : Payload (aspis_core.field.QM31.ZERO)) : Result aspis_core.field.QM31 := do
  let sum := out
  prover.inactive_sum_k_loop values masks sum 0#usize


end R1Z.PV_RE_ComposedSuffix030
pv_composed_source_contexts ProverRwFull.prover.inactive_sum_k
pv_composed_source_contexts R1Z.PV_RE_ComposedSuffix030.continueAfter

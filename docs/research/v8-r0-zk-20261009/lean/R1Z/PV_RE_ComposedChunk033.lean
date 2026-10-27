import R1Z.PV_RE_ComposedContextsGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix033
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.opening_inactive`.
Recursive calls remain the original extracted calls. -/
def continueAfter (q : Slice aspis_core.field.wide_exact.WideExact) (w : weights.Weights) (out : Payload (aspis_core.field.wide_exact.WideExact.ZERO)) : Result aspis_core.field.wide_exact.WideExact := do
  let inactive := out
  prover.opening_inactive_loop q w inactive 0#usize


end R1Z.PV_RE_ComposedSuffix033
pv_composed_source_contexts ProverRwFull.prover.opening_inactive
pv_composed_source_contexts R1Z.PV_RE_ComposedSuffix033.continueAfter

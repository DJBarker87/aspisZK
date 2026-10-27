import R1Z.PV_RE_ComposedContextsGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix029
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.fixed_k_column`.
Recursive calls remain the original extracted calls. -/
def continueAfter (values : Slice aspis_core.field.QM31) (out : Payload (aspis_core.field.QM31.ZERO)) : Result (Array aspis_core.field.QM31 1024#usize) := do
  let q := out
  let out := Array.repeat 1024#usize q
  prover.fixed_k_column_loop values out 0#usize


end R1Z.PV_RE_ComposedSuffix029
pv_composed_source_contexts ProverRwFull.prover.fixed_k_column
pv_composed_source_contexts R1Z.PV_RE_ComposedSuffix029.continueAfter

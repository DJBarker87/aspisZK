import R1Z.PV_RE_ComposedContextsGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix037
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.semantic_error`.
Recursive calls remain the original extracted calls. -/
def continueAfter (e : r1_wire.Error) (out : Payload (r1_wire.Error.Insts.CoreCmpPartialEqError.eq e r1_wire.Error.ActivePole)) : Result verifier.Error := do
  let b := out
  if b
  then ok verifier.Error.Rejected
  else ok verifier.Error.Semantic


end R1Z.PV_RE_ComposedSuffix037
pv_composed_source_contexts ProverRwFull.prover.semantic_error
pv_composed_source_contexts R1Z.PV_RE_ComposedSuffix037.continueAfter

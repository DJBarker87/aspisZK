import R1Z.PV_RE_ComposedContextsGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix049
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut`.
Recursive calls remain the original extracted calls. -/
def continueAfter (state : host_commitment.encode_commitment_words.closure_1) (args : Std.Usize) (out : Payload (host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError.call
      state args)) : Result ((core.result.Result host_commitment.Word aspis_core.r0.Error) ×
    host_commitment.encode_commitment_words.closure_1) := do
  let r := out
  ok (r, state)


end R1Z.PV_RE_ComposedSuffix049
pv_composed_source_contexts ProverRwFull.host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut
pv_composed_source_contexts R1Z.PV_RE_ComposedSuffix049.continueAfter

import R1Z.PV_RE_NoCatchGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix050
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError.call_once`.
Recursive calls remain the original extracted calls. -/
def continueAfter (c : host_commitment.encode_commitment_words.closure_1) (i : Std.Usize) (out : Payload (host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut
      c i)) : Result (core.result.Result host_commitment.Word aspis_core.r0.Error) := do
  let (r, _) := out
  ok r


end R1Z.PV_RE_NoCatchSuffix050
pv_no_catch_binds ProverRwFull.host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError.call_once
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix050.continueAfter

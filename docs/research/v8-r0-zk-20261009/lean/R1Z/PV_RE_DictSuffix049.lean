import R1Z.PV_RE_DictSuffix048
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix049
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


end R1Z.PV_RE_DictSuffix049
pv_dict_congr ProverRwFull.host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut
pv_dict_congr R1Z.PV_RE_DictSuffix049.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix049.continueAfter

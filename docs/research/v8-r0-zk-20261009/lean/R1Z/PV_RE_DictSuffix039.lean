import R1Z.PV_RE_DictSuffix038
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix039
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultStateOnlyAttemptSecretsError.call_once`.
Recursive calls remain the original extracted calls. -/
def continueAfter {T0 : Type} (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst :
  core.ops.function.FnMut T0 Std.Usize (Array Std.U8 32#usize)) (c : RealR1_client.prove_for_proof_accounts.closure T0) (i : Std.Usize) (out : Payload (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError.call_mut
      coreopsfunctionFnMutT0TupleUsizeArrayU832Inst c i)) : Result ((core.result.Result
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets verifier.Error) ×
    (RealR1_client.prove_for_proof_accounts.closure T0)) := do
  let (r, c1, call_mut_back) := out
  ok (r, call_mut_back c1)


end R1Z.PV_RE_DictSuffix039
pv_dict_congr ProverRwFull.RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultStateOnlyAttemptSecretsError.call_once
pv_dict_congr R1Z.PV_RE_DictSuffix039.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultStateOnlyAttemptSecretsError.call_once
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix039.continueAfter

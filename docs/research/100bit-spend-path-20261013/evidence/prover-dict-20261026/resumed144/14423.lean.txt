import R1Z.PDict_FmtClient0
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FmtErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Formatter irrelevance for the complete emitted `RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultStateOnlyAttemptSecretsError.call_once`. -/
theorem client_4 (ops other : ExternalFuns) :
    @RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultStateOnlyAttemptSecretsError.call_once _ (replace ops other) = @RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultStateOnlyAttemptSecretsError.call_once _ ops := by
  delta RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultStateOnlyAttemptSecretsError.call_once
  try simp only [client_3 ops other]
  all_goals rfl
#print axioms client_4

/-- Formatter irrelevance for the complete emitted `RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultStateOnlyAttemptSecretsError`. -/
theorem client_5 (ops other : ExternalFuns) :
    @RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultStateOnlyAttemptSecretsError _ (replace ops other) = @RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultStateOnlyAttemptSecretsError _ ops := by
  delta RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultStateOnlyAttemptSecretsError
  try simp only [client_4 ops other]
  all_goals rfl
#print axioms client_5

/-- Formatter irrelevance for the complete emitted `RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError`. -/
theorem client_6 (ops other : ExternalFuns) :
    @RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError _ (replace ops other) = @RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError _ ops := by
  delta RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError
  try simp only [client_3 ops other, client_5 ops other]
  all_goals rfl
#print axioms client_6

/-- Formatter irrelevance for the complete emitted `prover.prove_masked_retrying_with`. -/
theorem client_7 (ops other : ExternalFuns) :
    @prover.prove_masked_retrying_with _ (replace ops other) = @prover.prove_masked_retrying_with _ ops := by
  delta prover.prove_masked_retrying_with
  try simp only [erase_425 ops other, erase_361 ops other]
  all_goals rfl
#print axioms client_7
end R1Z.PDict_FmtErase

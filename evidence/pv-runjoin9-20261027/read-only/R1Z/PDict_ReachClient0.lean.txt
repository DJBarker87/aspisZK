import R1Z.PDict_ReachRetryComplete
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_ReachErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Absent-field irrelevance for the complete emitted `aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body`. -/
theorem client_0 (ops other : ExternalFuns) :
    @aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body _ (replace ops other) = @aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body _ ops := by
  delta aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
  try simp only [erase_62 ops other, erase_64 ops other]
  all_goals rfl
#print axioms client_0

/-- Absent-field irrelevance for the complete emitted `aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop`. -/
theorem client_1 (ops other : ExternalFuns) :
    @aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop _ (replace ops other) = @aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop _ ops := by
  delta aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop
  try simp only [client_0 ops other]
  all_goals rfl
#print axioms client_1

/-- Absent-field irrelevance for the complete emitted `aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce`. -/
theorem client_2 (ops other : ExternalFuns) :
    @aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce _ (replace ops other) = @aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce _ ops := by
  delta aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce
  try simp only [client_1 ops other]
  all_goals rfl
#print axioms client_2

/-- Absent-field irrelevance for the complete emitted `RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError.call_mut`. -/
theorem client_3 (ops other : ExternalFuns) :
    @RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError.call_mut _ (replace ops other) = @RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError.call_mut _ ops := by
  delta RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError.call_mut
  try simp only [client_2 ops other]
  all_goals rfl
#print axioms client_3
end R1Z.PDict_ReachErase

import PV_STX_EntropyCleanup
set_option autoImplicit false
noncomputable section
namespace PV_STX_CleanupBridge
open Aeneas Aeneas.Std ProverRwFull PV_STX_Code PV_STX_DenoteRules PV_STX_EntropyCleanup
variable [ExternalTypes] [ExternalFuns]
/-- The Rust cleanup reconstruction preserves the entire extracted Result
on the erasure interpretation. This law does not assert native drop silence. -/
theorem loop_erases (nonce : Array U8 32#usize) (limit retry : Usize) :
    denote fixed (entropyLoop nonce limit retry) =
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop nonce limit retry := by
  simp only [entropyLoop,loop_rule,body_erases,
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop]

theorem generate_erases (nonce : Array U8 32#usize) :
    denote fixed (generate nonce) =
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce nonce := by
  simp only [generate,bind_rule,nonzero_erases,if_rule,loop_erases,pure_rule,
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce]

#print axioms loop_erases
#print axioms generate_erases
end PV_STX_CleanupBridge

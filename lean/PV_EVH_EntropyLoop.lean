import PV_EVH_Entropy
import PV_EVH_WorldLoop
set_option autoImplicit false
noncomputable section
namespace PV_EVH_EntropyLoop
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_World PV_EVH_WorldLoop PV_EVH_Entropy
variable [ExternalTypes] [ExternalFuns]

/-- Stateful interpretation of the existing emitted entropy loop, before
Result evaluation. This is a prover SUBPROGRAM, not the proof-account entry. -/
def entropyRun (fuel : Nat) (answers : EntropyAnswers)
    (nonce : Array U8 32#usize) (limit retry : Usize) : World → Prefix
      (core.result.Result aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
        aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError) :=
  PV_EVH_WorldLoop.loop (entropyBody answers nonce limit) fuel retry

/-- No regression on the fixed-answer view, for every completed finite run.
The reject-zero then successful draw world is deliberately outside this view. -/
theorem entropyRun_fixed (fuel : Nat) (answers : EntropyAnswers)
    (same : ∀ n s, answers n s = getrandom.fill s)
    (nonce : Array U8 32#usize) (limit retry : Usize) (w : World)
    (r : Result (core.result.Result
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
      aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError))
    (finished : (entropyRun fuel answers nonce limit retry w).status = .finished r) :
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop nonce limit retry = r := by
  exact fixed_finished (entropyBody answers nonce limit)
    (fun i => aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body nonce limit i)
    (fun i => entropyBody_fixed answers same nonce limit i) fuel retry w r finished

#print axioms entropyRun_fixed
end PV_EVH_EntropyLoop

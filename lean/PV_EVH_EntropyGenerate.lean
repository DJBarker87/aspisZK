import PV_EVH_Prefix
import PV_EVH_EntropyLoop
set_option autoImplicit false
noncomputable section
namespace PV_EVH_EntropyGenerate
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World PV_EVH_WorldLoop
open PV_EVH_Prefix (P FinishedView)
open PV_EVH_Entropy (EntropyAnswers)
variable [ExternalTypes] [ExternalFuns]
abbrev Secrets := aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
abbrev EntropyError := aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError

/-- Exact outer source guard, then the existing finite entropy interpretation.
The inherited entropyBody afterDraw still has explicit event-coverage gaps. -/
def generate (fuel : Nat) (answers : EntropyAnswers)
    (nonce : Array U8 32#usize) : P (core.result.Result Secrets EntropyError) := do
  let b ← PV_EVH_Prefix.lift (aspis_prover.state_only_entropy.entropy_nonzero32 nonce)
  if b then
    PV_EVH_EntropyLoop.entropyRun fuel answers nonce
      aspis_prover.state_only_entropy.ENTROPY_RETRY_LIMIT 0#usize
  else
    pure (.Err .RepeatedZeroBlock)

theorem generate_fixed (fuel : Nat) (answers : EntropyAnswers)
    (same : ∀ n s, answers n s = getrandom.fill s)
    (nonce : Array U8 32#usize) :
    FinishedView (generate fuel answers nonce)
      (aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce nonce) := by
  unfold generate aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce
  apply PV_EVH_Prefix.bind_fixed
  · exact PV_EVH_Prefix.lift_fixed _
  · intro b
    cases b with
    | false => exact PV_EVH_Prefix.lift_fixed _
    | true =>
      intro w r finished
      exact PV_EVH_EntropyLoop.entropyRun_fixed fuel answers same nonce
        aspis_prover.state_only_entropy.ENTROPY_RETRY_LIMIT 0#usize w r finished

#print axioms generate_fixed
end PV_EVH_EntropyGenerate

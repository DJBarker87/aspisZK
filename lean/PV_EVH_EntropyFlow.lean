import PV_EVH_EntropyStep
import PV_EVH_PrefixLoop
set_option autoImplicit false
noncomputable section
namespace PV_EVH_EntropyFlow
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
open PV_EVH_Entropy (EntropyAnswers)
variable [ExternalTypes] [ExternalFuns]
abbrev Secrets := aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
abbrev EntropyError := aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError

/-- Source entropy recursion with each formerly erased afterDraw callee exposed.
Nested exhaustion and every callee's events survive. Native leaf laws are OPEN. -/
def loop (fuel : Nat) (answers : EntropyAnswers) (c : PV_EVH_EntropyStep.Callees)
    (nonce : Array U8 32#usize) (limit retry : Usize) : P (core.result.Result Secrets EntropyError) :=
  PV_EVH_PrefixLoop.loop (fun i => PV_EVH_EntropyStep.run nonce limit i answers c) fuel retry

theorem loop_fixed (fuel : Nat) (answers : EntropyAnswers) (c : PV_EVH_EntropyStep.Callees)
    (hc : PV_EVH_EntropyStep.Compatible c)
    (same : ∀ n s, answers n s = getrandom.fill s)
    (nonce : Array U8 32#usize) (limit retry : Usize) :
    FinishedView (loop fuel answers c nonce limit retry)
      (Secrets.generate_for_mask_nonce_loop nonce limit retry) := by
  apply PV_EVH_PrefixLoop.fixed_recursive
    (fun i => PV_EVH_EntropyStep.run nonce limit i answers c)
    (fun i => Secrets.generate_for_mask_nonce_loop.body nonce limit i)
    (fun i => Secrets.generate_for_mask_nonce_loop nonce limit i)
  · intro i
    unfold Secrets.generate_for_mask_nonce_loop
    rw [Aeneas.Std.loop.eq_def]
  · intro i
    exact PV_EVH_EntropyStep.run_fixed nonce limit i answers c hc same

/-- The outer source guard is also explicitly unfinished, never Result-lifted. -/
def generate (fuel : Nat) (answers : EntropyAnswers) (c : PV_EVH_EntropyStep.Callees)
    (nonzero_OPEN : Array U8 32#usize → P Bool) (nonce : Array U8 32#usize) :
    P (core.result.Result Secrets EntropyError) := do
  let b ← nonzero_OPEN nonce
  if b then loop fuel answers c nonce aspis_prover.state_only_entropy.ENTROPY_RETRY_LIMIT 0#usize
  else pure (.Err .RepeatedZeroBlock)

theorem generate_fixed (fuel : Nat) (answers : EntropyAnswers) (c : PV_EVH_EntropyStep.Callees)
    (hc : PV_EVH_EntropyStep.Compatible c)
    (same : ∀ n s, answers n s = getrandom.fill s)
    (nonzero_OPEN : Array U8 32#usize → P Bool)
    (hn : ∀ n, FinishedView (nonzero_OPEN n) (aspis_prover.state_only_entropy.entropy_nonzero32 n))
    (nonce : Array U8 32#usize) :
    FinishedView (generate fuel answers c nonzero_OPEN nonce) (Secrets.generate_for_mask_nonce nonce) := by
  unfold generate Secrets.generate_for_mask_nonce
  apply PV_EVH_Prefix.bind_fixed
  · exact hn nonce
  · intro b
    cases b with
    | false => exact PV_EVH_Prefix.lift_fixed _
    | true => exact loop_fixed fuel answers c hc same nonce _ _

#print axioms loop_fixed
#print axioms generate_fixed
end PV_EVH_EntropyFlow

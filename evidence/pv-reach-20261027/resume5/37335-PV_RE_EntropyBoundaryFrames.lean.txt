import R1Z.PV_RE_RetryStep
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_EntropyBoundaryFrames
open Aeneas.Std ProverRwFull PV_RE_RetryStep
variable [ExternalTypes] [ExternalFuns]
abbrev RawEntropy (C : Type) := core.ops.function.FnMut C Usize (Array U8 32#usize)

/-- The generated client closure forwards an outer error from the supplied
entropy trait call. The exact extracted call_mut body justifies this boundary. -/
theorem closure_failure {C : Type} (entropy : RawEntropy C) (state : C)
    (k : Usize) (e : Error) (h : entropy.call_mut state k = .fail e) :
    RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError.call_mut
      entropy state k = .fail e := by
  unfold RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError.call_mut
  rw [h]
  rfl

/-- The FnMut dictionary wrapper restores state only after outer success. -/
theorem trait_failure {C : Type} (entropy : RawEntropy C) (state : C)
    (k : Usize) (e : Error) (h : entropy.call_mut state k = .fail e) :
    (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError
      entropy).call_mut state k = .fail e := by
  change (do
    let (r, c1, back) ←
      RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError.call_mut
        entropy state k
    Result.ok (r, back c1)) = .fail e
  rw [closure_failure entropy state k e h]
  rfl

/-- The named fixed-point equation is used once; no run is normalized. -/
theorem retry_failure {C : Type} (entropy : Entropy C) (pub : Public)
    (compiled : Compiled) (variant : transport.Variant) (hash : Hash)
    (store : Store) (state : C) (k : Usize) (e : Error)
    (active : ¬ k >= prover.ATTEMPT_CAP)
    (h : entropy.call_mut state k = .fail e) :
    prover.retry_attempt entropy pub compiled variant hash store state k = .fail e := by
  rw [PV_RE_RetryStep.unfold_retry]
  unfold PV_RE_RetryStep.step
  rw [if_neg active, h]
  rfl

/-- A divergence at this actual trait boundary also propagates. -/
theorem retry_divergence {C : Type} (entropy : Entropy C) (pub : Public)
    (compiled : Compiled) (variant : transport.Variant) (hash : Hash)
    (store : Store) (state : C) (k : Usize)
    (active : ¬ k >= prover.ATTEMPT_CAP)
    (h : entropy.call_mut state k = .div) :
    prover.retry_attempt entropy pub compiled variant hash store state k = .div := by
  rw [PV_RE_RetryStep.unfold_retry]
  unfold PV_RE_RetryStep.step
  rw [if_neg active, h]
  rfl

#print axioms closure_failure
#print axioms trait_failure
#print axioms retry_failure
#print axioms retry_divergence
end R1Z.PV_RE_EntropyBoundaryFrames

import R1Z.ProverRwEffectRetry
import R1Z.ProverRwEntropyIteration
import R1Z.GamesR1

/-! Source boundary only. This module does not assert a deployed FS instance.
The world interpreter and the fixed external dictionary are distinct. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_Source
open Aeneas Aeneas.Std Result ProverRwFull
open R0Z.FsStatement R1Z.GamesR1

/-- V046: the existing complete observer-program carrier has a concrete member. -/
def idleObserver {K CommitHandle Aux : Type} [Field K] : R1Adv K CommitHandle Aux :=
  ⟨fun _ _ => .done, fun _ => false⟩

theorem observer_nonempty {K CommitHandle Aux : Type} [Field K] :
    Nonempty (R1Adv K CommitHandle Aux) := ⟨idleObserver⟩

/-- Literal proof-account entry, for the supplied external dictionary. There
is no entropy/world, native dictionary or byte/view adequacy assertion here. -/
theorem proof_accounts_entry [ExternalTypes] [ExternalFuns] {C : Type}
    (account : ProverRwEffectCallback.Account C)
    (pub : ProverRwRetryModel.Pub) (compiled : ProverRwRetryModel.Compiled)
    (hash : ProverRwRetryModel.Hash) (store : ProverRwRetryModel.Store) (state : C) :
    RealR1_client.prove_for_proof_accounts account pub compiled hash store state =
      prover.prove_masked_retrying_with
        (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError account)
        pub compiled .S2 hash store state := by
  unfold RealR1_client.prove_for_proof_accounts
  cases prover.prove_masked_retrying_with
    (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError account)
    pub compiled .S2 hash store state <;> rfl

/-- The fixed-dictionary emitted body cannot realize a reject-then-success
entropy path, even if its dictionary is chosen separately for each whole run.
This is not a counterexample to the native effectful prover. -/
theorem fixed_dictionary_obstruction [ExternalTypes] (ops : ExternalFuns)
    (nonce : Array U8 32#usize) (secret : ProverRwEntropyIteration.Secret) :
    letI : ExternalFuns := ops
    ¬ (ProverRwEntropyIteration.Body nonce 16#usize 0#usize = .ok (.cont 1#usize) ∧
       ProverRwEntropyIteration.Body nonce 16#usize 1#usize = .ok (.done (.Ok secret))) := by
  letI : ExternalFuns := ops
  exact ProverRwEntropyIteration.no_retry_then_success nonce 16#usize 0#usize 1#usize
    1#usize (by decide) (by decide) secret

#print axioms idleObserver
#print axioms observer_nonempty
#print axioms proof_accounts_entry
#print axioms fixed_dictionary_obstruction
end R1Z.PV_RunJoin_Source

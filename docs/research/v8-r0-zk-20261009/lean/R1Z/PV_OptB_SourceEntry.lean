import R1Z.PV_OptB_SourceFirstFailure
set_option autoImplicit false
namespace R1Z.PV_OptB_SourceEntry
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
variable [ExternalTypes] [ExternalFuns]

theorem entry {S : Type} (account : ProverRwEffectCallback.Account S)
    (pub : Pub) (compiled : Compiled) (hash : Hash) (store : Store) (state : S)
    (variant : core.cmp.PartialEq.ne.trait_default
      transport.Variant.Insts.CoreCmpPartialEqVariant .S2 .S2 = .ok false) :
    RealR1_client.prove_for_proof_accounts account pub compiled hash store state =
      prover.retry_attempt
        (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError account)
        pub compiled .S2 hash store state 0#usize := by
  unfold RealR1_client.prove_for_proof_accounts prover.prove_masked_retrying_with
  rw [variant]
  simp only [bind_tc_ok,Bool.false_eq_true,if_false]
  cases prover.retry_attempt
      (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError account)
      pub compiled .S2 hash store state 0#usize <;> rfl

#print axioms entry
end R1Z.PV_OptB_SourceEntry

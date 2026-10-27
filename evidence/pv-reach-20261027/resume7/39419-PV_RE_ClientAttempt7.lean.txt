import R1Z.PV_RE_ClientPrefix6
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ClientAttempt7
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep
variable [ExternalTypes]

/-- The whole original client enters its first attempt under these two exact
source prefix equations. The returned continuation is the retry continuation. -/
theorem client_to_attempt {C : Type} (D : ExternalFuns)
    (entropy : core.ops.function.FnMut C Usize (Array U8 32#usize))
    (pub : Public) (compiled : Compiled) (hash : Hash) (store : Store)
    (state state1 : C) (secret : Secrets)
    (guard : D.op233 .S2 .S2 = .ok true)
    (entropy_prefix :
      (@RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError
        _ D C entropy).call_mut state 0#usize = .ok (.Ok secret,state1)) :
    ∃ next, @RealR1_client.prove_for_proof_accounts _ D C entropy pub compiled hash store state =
      (@prover.prove_masked_attempt _ D pub compiled .S2 hash secret store >>= next) := by
  rw [PV_RE_ClientPrefix6.client_to_retry D entropy pub compiled hash store state guard]
  exact PV_RE_ClientPrefix6.retry_to_attempt D _ pub compiled .S2 hash store state state1 0#usize
    secret PV_RE_CapValue.below_cap entropy_prefix

/-- Compose a checked original-attempt prefix through the actual client and
retry binds. This does not discharge the prefix equations or fixture laws. -/
theorem lift_prefix {C A : Type} (D : ExternalFuns)
    (entropy : core.ops.function.FnMut C Usize (Array U8 32#usize))
    (pub : Public) (compiled : Compiled) (hash : Hash) (store : Store)
    (state state1 : C) (secret : Secrets)
    (guard : D.op233 .S2 .S2 = .ok true)
    (entropy_prefix :
      (@RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError
        _ D C entropy).call_mut state 0#usize = .ok (.Ok secret,state1))
    (call : Result A)
    (source_prefix : ∃ next,
      @prover.prove_masked_attempt _ D pub compiled .S2 hash secret store = (call >>= next)) :
    ∃ next, @RealR1_client.prove_for_proof_accounts _ D C entropy pub compiled hash store state =
      (call >>= next) := by
  obtain ⟨retry, hr⟩ := client_to_attempt D entropy pub compiled hash store state state1 secret
    guard entropy_prefix
  obtain ⟨suffix, hs⟩ := source_prefix
  rw [hr,hs,PV_RE_ClientEntry.bind_assoc]
  exact ⟨_,rfl⟩
#print axioms client_to_attempt
#print axioms lift_prefix
end R1Z.PV_RE_ClientAttempt7

import R1Z.PV_RE_ClientPrefix6
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_PublicPrefix6
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep
variable [ExternalTypes]
abbrev RawEntropy (C : Type) := core.ops.function.FnMut C Usize (Array U8 32#usize)
abbrev EntropyWrapper {C : Type} (D : ExternalFuns) (entropy : RawEntropy C) :=
  @RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError _ D C entropy

/-- All prefix hypotheses are concrete equations on the original extracted
calls, with their returned values retained. No fixture admission is assumed. -/
theorem client_to_public {C : Type} (D : ExternalFuns)
    (entropy : RawEntropy C) (pub : Public) (compiled : Compiled) (hash : Hash)
    (store : Store) (state state1 : C) (secret : Secrets)
    (guard : D.op233 .S2 .S2 = .ok true)
    (entropy_prefix : (EntropyWrapper D entropy).call_mut state 0#usize =
      .ok (.Ok secret,state1)) :
    ∃ next,
      @RealR1_client.prove_for_proof_accounts _ D C entropy pub compiled hash store state =
        (D.op226 pub >>= next) := by
  letI : ExternalFuns := D
  rw [PV_RE_ClientPrefix6.client_to_retry D entropy pub compiled hash store state guard]
  obtain ⟨next, hn⟩ := PV_RE_ClientPrefix6.retry_to_attempt D
    (EntropyWrapper D entropy) pub compiled .S2 hash store state state1 0#usize secret
    PV_RE_CapValue.below_cap entropy_prefix
  rw [hn]
  obtain ⟨suffix, hs⟩ := PV_RE_AttemptEntry.first D pub compiled .S2 hash secret store
  rw [hs, PV_RE_ClientEntry.bind_assoc]
  exact ⟨_,rfl⟩

/-- If this reached public-serialization call fails, the original complete
client fails. The entropy-prefix equation is checked for this same dictionary. -/
theorem client_public_failure {C : Type} (D : ExternalFuns)
    (entropy : RawEntropy C) (pub : Public) (compiled : Compiled) (hash : Hash)
    (store : Store) (state state1 : C) (secret : Secrets)
    (guard : D.op233 .S2 .S2 = .ok true)
    (entropy_prefix : (EntropyWrapper D entropy).call_mut state 0#usize =
      .ok (.Ok secret,state1)) (e : Error) (poison : D.op226 pub = .fail e) :
    @RealR1_client.prove_for_proof_accounts _ D C entropy pub compiled hash store state =
      .fail e := by
  obtain ⟨next,hn⟩ := client_to_public D entropy pub compiled hash store state state1 secret
    guard entropy_prefix
  rw [hn,poison]
  rfl

#print axioms EntropyWrapper
#print axioms client_to_public
#print axioms client_public_failure
end R1Z.PV_RE_PublicPrefix6

import R1Z.PV_RE_AttemptHashPrefix6
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ClientHashPrefix6
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep PV_RE_PublicPrefix6
open PV_RE_AttemptHashPrefix6
variable [ExternalTypes]

/-- Original client to its first supplied hash, preserving the successful
variant, entropy and public serialization prefix equations. -/
theorem client_to_hash {C : Type} (D : ExternalFuns)
    (entropy : RawEntropy C) (pub : Public) (compiled : Compiled) (hash : Hash)
    (store : Store) (state state1 : C) (secret : Secrets) (bytes : alloc.vec.Vec U8)
    (guard : D.op233 .S2 .S2 = .ok true)
    (entropy_prefix : (EntropyWrapper D entropy).call_mut state 0#usize =
      .ok (.Ok secret,state1))
    (serialization : D.op226 pub = .ok (.Ok bytes))
    (map_error : D.op12
      prover.prove_masked_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
      (.Ok bytes) () = .ok (.Ok bytes)) :
    ∃ next,
      @RealR1_client.prove_for_proof_accounts _ D C entropy pub compiled hash store state =
        (hash (publicFrame bytes) >>= next) := by
  letI : ExternalFuns := D
  rw [PV_RE_ClientPrefix6.client_to_retry D entropy pub compiled hash store state guard]
  obtain ⟨next, hn⟩ := PV_RE_ClientPrefix6.retry_to_attempt D
    (EntropyWrapper D entropy) pub compiled .S2 hash store state state1 0#usize secret
    PV_RE_CapValue.below_cap entropy_prefix
  rw [hn]
  obtain ⟨suffix, hs⟩ := attempt_to_hash D pub compiled .S2 hash secret store bytes serialization map_error
  rw [hs, PV_RE_ClientEntry.bind_assoc]
  exact ⟨_,rfl⟩

/-- The same actual prefixes are independent of the supplied hash parameter;
poisoning that hash therefore fails the original complete client. -/
theorem poisoned_hash_failure {C : Type} (D : ExternalFuns)
    (entropy : RawEntropy C) (pub : Public) (compiled : Compiled)
    (store : Store) (state state1 : C) (secret : Secrets) (bytes : alloc.vec.Vec U8)
    (guard : D.op233 .S2 .S2 = .ok true)
    (entropy_prefix : (EntropyWrapper D entropy).call_mut state 0#usize =
      .ok (.Ok secret,state1))
    (serialization : D.op226 pub = .ok (.Ok bytes))
    (map_error : D.op12
      prover.prove_masked_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
      (.Ok bytes) () = .ok (.Ok bytes)) (e : Error) :
    @RealR1_client.prove_for_proof_accounts _ D C entropy pub compiled
      (fun _ => .fail e) store state = .fail e := by
  obtain ⟨next, hn⟩ := client_to_hash D entropy pub compiled (fun _ => .fail e)
    store state state1 secret bytes guard entropy_prefix serialization map_error
  rw [hn]
  rfl

#print axioms client_to_hash
#print axioms poisoned_hash_failure
end R1Z.PV_RE_ClientHashPrefix6

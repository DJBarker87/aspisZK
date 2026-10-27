import R1Z.PV_RE_ClientTag7
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Poison2347
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep PV_RE_AttemptHashPrefix6 PV_RE_AttemptContext7 PV_RE_PublicPrefix6
variable [ExternalTypes]
def poison (D : ExternalFuns) (e : Error) : ExternalFuns :=
  {D with op234 := fun _ => .fail e}
theorem poisoned_client_failure {C : Type} (D : ExternalFuns)
    (entropy : RawEntropy C) (pub : Public) (compiled : Compiled) (hash : Hash)
    (store : Store) (state state1 : C) (secret : Secrets)
    (guard : D.op233 .S2 .S2 = .ok true)
    (entropy_prefix : (EntropyWrapper D entropy).call_mut state 0#usize =
      .ok (.Ok secret,state1))
    (bytes : alloc.vec.Vec U8) (digest : Array U8 32#usize)
    (serialization : D.op226 pub = .ok (.Ok bytes))
    (map_error : D.op12
      prover.prove_masked_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
      (.Ok bytes) () = .ok (.Ok bytes))
    (first_hash : hash (publicFrame bytes) = .ok digest)
    (context : Context)
    (context_prefix : D.op115 digest secret.mask_nonce = .ok context) (e : Error) :
    @RealR1_client.prove_for_proof_accounts _ (poison D e) C entropy pub compiled hash store state =
      .fail e := by
  obtain ⟨next,hn⟩ := PV_RE_ClientTag7.client_to_tag (poison D e) entropy pub compiled hash store state state1 secret guard entropy_prefix bytes digest serialization map_error first_hash context context_prefix
  rw [hn]
  rfl
#print axioms poison
#print axioms poisoned_client_failure
theorem success_distinguishes {C : Type} (D : ExternalFuns)
    (entropy : RawEntropy C) (pub : Public) (compiled : Compiled) (hash : Hash)
    (store : Store) (state state1 : C) (secret : Secrets)
    (guard : D.op233 .S2 .S2 = .ok true)
    (entropy_prefix : (EntropyWrapper D entropy).call_mut state 0#usize =
      .ok (.Ok secret,state1))
    (bytes : alloc.vec.Vec U8) (digest : Array U8 32#usize)
    (serialization : D.op226 pub = .ok (.Ok bytes))
    (map_error : D.op12
      prover.prove_masked_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
      (.Ok bytes) () = .ok (.Ok bytes))
    (first_hash : hash (publicFrame bytes) = .ok digest)
    (context : Context)
    (context_prefix : D.op115 digest secret.mask_nonce = .ok context) (e : Error)
    (v : (core.result.Result prover.RetriedProof verifier.Error) × Store)
    (success : @RealR1_client.prove_for_proof_accounts _ D C
      entropy pub compiled hash store state = .ok v) :
    @RealR1_client.prove_for_proof_accounts _ (poison D e) C entropy pub compiled hash store state ≠
      @RealR1_client.prove_for_proof_accounts _ D C entropy pub compiled hash store state := by
  rw [poisoned_client_failure D entropy pub compiled hash store state state1 secret guard entropy_prefix bytes digest serialization map_error first_hash context context_prefix e, success]
  intro h
  cases h
#print axioms success_distinguishes
end R1Z.PV_RE_Poison2347

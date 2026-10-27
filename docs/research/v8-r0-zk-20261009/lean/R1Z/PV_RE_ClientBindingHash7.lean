import R1Z.PV_RE_AttemptBindingHash7
import R1Z.PV_RE_ClientAttempt7
import R1Z.PV_RE_PublicPrefix6
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ClientBindingHash7
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep PV_RE_AttemptHashPrefix6 PV_RE_AttemptContext7 PV_RE_PublicPrefix6
open PV_RE_AttemptBindingHash7
variable [ExternalTypes]
theorem client_to_bindinghash {C : Type} (D : ExternalFuns)
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
    (context_prefix : D.op115 digest secret.mask_nonce = .ok context)
    (tag : U8) (tag_prefix : D.op234 .S2 = .ok tag)
    (encoded : Array U8 81#usize) (encode_prefix : D.op116 context = .ok encoded) :
    ∃ next, @RealR1_client.prove_for_proof_accounts _ D C entropy pub compiled hash store state =
      (hash (bindingFrame bytes tag encoded) >>= next) := by
  apply PV_RE_ClientAttempt7.lift_prefix D entropy pub compiled hash store state state1 secret
    guard entropy_prefix (hash (bindingFrame bytes tag encoded))
  exact PV_RE_AttemptBindingHash7.attempt_to_bindinghash D pub compiled .S2 hash secret store bytes digest serialization map_error first_hash context context_prefix tag tag_prefix encoded encode_prefix
#print axioms client_to_bindinghash
theorem client_failure {C : Type} (D : ExternalFuns)
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
    (context_prefix : D.op115 digest secret.mask_nonce = .ok context)
    (tag : U8) (tag_prefix : D.op234 .S2 = .ok tag)
    (encoded : Array U8 81#usize) (encode_prefix : D.op116 context = .ok encoded) (e : Error)
    (call_failure : hash (bindingFrame bytes tag encoded) = .fail e) :
    @RealR1_client.prove_for_proof_accounts _ D C entropy pub compiled hash store state = .fail e := by
  obtain ⟨next,hn⟩ := client_to_bindinghash D entropy pub compiled hash store state state1 secret
    guard entropy_prefix bytes digest serialization map_error first_hash context context_prefix tag tag_prefix encoded encode_prefix
  rw [hn,call_failure]
  rfl
#print axioms client_failure
theorem client_divergence {C : Type} (D : ExternalFuns)
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
    (context_prefix : D.op115 digest secret.mask_nonce = .ok context)
    (tag : U8) (tag_prefix : D.op234 .S2 = .ok tag)
    (encoded : Array U8 81#usize) (encode_prefix : D.op116 context = .ok encoded)
    (call_divergence : hash (bindingFrame bytes tag encoded) = .div) :
    @RealR1_client.prove_for_proof_accounts _ D C entropy pub compiled hash store state = .div := by
  obtain ⟨next,hn⟩ := client_to_bindinghash D entropy pub compiled hash store state state1 secret
    guard entropy_prefix bytes digest serialization map_error first_hash context context_prefix tag tag_prefix encoded encode_prefix
  rw [hn,call_divergence]
  rfl
#print axioms client_divergence
end R1Z.PV_RE_ClientBindingHash7

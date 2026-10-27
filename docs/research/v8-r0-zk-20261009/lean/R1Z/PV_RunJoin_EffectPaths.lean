import R1Z.PV_RunJoin_EffectClient
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EffectPaths
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRwRetryModel (Pub Compiled Hash Store Secret Proof)
open ProverRwEffectTape (World)
open PV_RunJoin_EffectClient
variable [ExternalTypes] [ExternalFuns]
variable {N : Type} (account : ProverRwEffectCallback.Account N)
  (pub : Pub) (compiled : Compiled) (hash : Hash) (index : Nat) (s : State N)

theorem policy_failure (e : Aeneas.Std.Error)
    (h : account.call_mut s.policy (ProverCommitRetrySource34.word index) = .fail e) :
    attempt account pub compiled hash index s = ⟨s,.failed e⟩ := by
  simp only [attempt,h]

theorem policy_divergence
    (h : account.call_mut s.policy (ProverCommitRetrySource34.word index) = .div) :
    attempt account pub compiled hash index s = ⟨s,.diverged⟩ := by
  simp only [attempt,h]

theorem native_entropy_error (nonce : Array U8 32#usize) (next : N)
    (world : World) (e : aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError)
    (hp : account.call_mut s.policy (ProverCommitRetrySource34.word index) = .ok (nonce,next))
    (he : ProverRwEffectOwner.worldOwner nonce s.entropy = ⟨.returned (.ok (.Err e)),world⟩) :
    attempt account pub compiled hash index s =
      ⟨⟨world,next,s.ledger⟩,.error .Entropy⟩ := by
  simp only [attempt,hp,he]

theorem body_rejection (nonce : Array U8 32#usize) (next : N)
    (world : World) (secret : Secret) (ledger : Store)
    (hp : account.call_mut s.policy (ProverCommitRetrySource34.word index) = .ok (nonce,next))
    (he : ProverRwEffectOwner.worldOwner nonce s.entropy = ⟨.returned (.ok (.Ok secret)),world⟩)
    (hb : prover.prove_masked_attempt pub compiled .S2 hash secret s.ledger = .ok (.Err .Rejected,ledger)) :
    attempt account pub compiled hash index s = ⟨⟨world,next,ledger⟩,.rejected⟩ := by
  simp only [attempt,hp,he,hb]

theorem body_success (nonce : Array U8 32#usize) (next : N)
    (world : World) (secret : Secret) (ledger : Store) (proof : Proof)
    (hp : account.call_mut s.policy (ProverCommitRetrySource34.word index) = .ok (nonce,next))
    (he : ProverRwEffectOwner.worldOwner nonce s.entropy = ⟨.returned (.ok (.Ok secret)),world⟩)
    (hb : prover.prove_masked_attempt pub compiled .S2 hash secret s.ledger = .ok (.Ok proof,ledger)) :
    attempt account pub compiled hash index s = ⟨⟨world,next,ledger⟩,.published proof (index+1)⟩ := by
  simp only [attempt,hp,he,hb]

theorem rejected_next (fuel : Nat) (after : State N)
    (h : attempt account pub compiled hash index s = ⟨after,.rejected⟩) :
    run account pub compiled hash (fuel+1) index s =
      run account pub compiled hash fuel (index+1) after := by
  simp only [run,h]

theorem cap (i : Nat) (state : State N) :
    run account pub compiled hash 0 i state = ⟨state,.error .AttemptsExhausted⟩ := rfl

#print axioms policy_failure
#print axioms policy_divergence
#print axioms native_entropy_error
#print axioms body_rejection
#print axioms body_success
#print axioms rejected_next
#print axioms cap
end R1Z.PV_RunJoin_EffectPaths

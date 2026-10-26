import R1Z.PV_RunJoin_EffectPaths
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EffectResiduals
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRwRetryModel (Pub Compiled Hash Store Secret)
open ProverRwEffectTape (World)
open ProverRwEffectSource (Reply Outcome)
open PV_RunJoin_EffectClient
variable [ExternalTypes] [ExternalFuns]
variable {N : Type} (account : ProverRwEffectCallback.Account N)
  (pub : Pub) (compiled : Compiled) (hash : Hash) (index : Nat) (s : State N)
  (nonce : Array U8 32#usize) (next : N) (world : World)
  (hp : account.call_mut s.policy (ProverCommitRetrySource34.word index) = .ok (nonce,next))

include hp

theorem entropy_failed (e : Aeneas.Std.Error)
    (he : ProverRwEffectOwner.worldOwner nonce s.entropy = ⟨.returned (.fail e),world⟩) :
    attempt account pub compiled hash index s = ⟨⟨world,next,s.ledger⟩,.failed e⟩ := by
  simp only [attempt,hp,he]

theorem entropy_diverged
    (he : ProverRwEffectOwner.worldOwner nonce s.entropy = ⟨.returned .div,world⟩) :
    attempt account pub compiled hash index s = ⟨⟨world,next,s.ledger⟩,.diverged⟩ := by
  simp only [attempt,hp,he]

theorem entropy_request (input : Slice U8) (resume : Reply → Result Outcome)
    (he : ProverRwEffectOwner.worldOwner nonce s.entropy = ⟨.request input resume,world⟩) :
    attempt account pub compiled hash index s = ⟨⟨world,next,s.ledger⟩,.request input resume⟩ := by
  simp only [attempt,hp,he]

theorem entropy_fuel (retry : Usize)
    (he : ProverRwEffectOwner.worldOwner nonce s.entropy = ⟨.retry retry,world⟩) :
    attempt account pub compiled hash index s = ⟨⟨world,next,s.ledger⟩,.entropyFuel retry⟩ := by
  simp only [attempt,hp,he]

theorem body_failed (secret : Secret) (e : Aeneas.Std.Error)
    (he : ProverRwEffectOwner.worldOwner nonce s.entropy = ⟨.returned (.ok (.Ok secret)),world⟩)
    (hb : prover.prove_masked_attempt pub compiled .S2 hash secret s.ledger = .fail e) :
    attempt account pub compiled hash index s = ⟨⟨world,next,s.ledger⟩,.failed e⟩ := by
  simp only [attempt,hp,he,hb]

theorem body_diverged (secret : Secret)
    (he : ProverRwEffectOwner.worldOwner nonce s.entropy = ⟨.returned (.ok (.Ok secret)),world⟩)
    (hb : prover.prove_masked_attempt pub compiled .S2 hash secret s.ledger = .div) :
    attempt account pub compiled hash index s = ⟨⟨world,next,s.ledger⟩,.diverged⟩ := by
  simp only [attempt,hp,he,hb]

theorem body_error (secret : Secret) (ledger : Store) (e : verifier.Error) (fatal : e ≠ .Rejected)
    (he : ProverRwEffectOwner.worldOwner nonce s.entropy = ⟨.returned (.ok (.Ok secret)),world⟩)
    (hb : prover.prove_masked_attempt pub compiled .S2 hash secret s.ledger = .ok (.Err e,ledger)) :
    attempt account pub compiled hash index s = ⟨⟨world,next,ledger⟩,.error e⟩ := by
  cases e <;> simp_all only [attempt,hp,he,hb,ne_eq,not_true_eq_false]

#print axioms entropy_failed
#print axioms entropy_diverged
#print axioms entropy_request
#print axioms entropy_fuel
#print axioms body_failed
#print axioms body_diverged
#print axioms body_error
end R1Z.PV_RunJoin_EffectResiduals

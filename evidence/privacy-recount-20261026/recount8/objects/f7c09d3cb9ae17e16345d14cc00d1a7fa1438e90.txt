import R1Z.ProverRwQueryNativeAttempt
import R1Z.ProverRwCallerBinding
set_option autoImplicit false
namespace R1Z.ProverRwQueryRetry
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
open ProverCommitSemanticTransport26
variable [ExternalTypes] [ExternalFuns]

def queryAttempt {C : Type} (entropy : Entropy C) (pub : Pub) (compiled : Compiled)
    (variant : transport.Variant) (hash : Hash) : ProverCommitRetry34.Attempt (C × Store) Proof :=
  fun k s => do
    let (r,after) ← entropy.call_mut s.1 (ProverCommitRetrySource34.word k)
    match r with
    | .Err e => ok (.stop (error e),(after,s.2))
    | .Ok secret =>
      let (r1,store) ← ProverRwQueryNativeAttempt.nativeAttempt pub compiled variant hash secret s.2
      match r1 with
      | .Ok p => ok (.done p,(after,store))
      | .Err .Rejected => ok (.retry,(after,store))
      | .Err e => ok (.stop (error e),(after,store))


set_option backward.isDefEq.respectTransparency false in
theorem attempt_transport {C : Type} (entropy : Entropy C) (pub : Pub)
    (compiled : Compiled) (variant : transport.Variant) (h : Hash) :
    ProverRwRetryModel.attempt entropy pub compiled variant h =
      queryAttempt entropy pub compiled variant h := by
  funext k s
  simp only [ProverRwRetryModel.attempt,queryAttempt,
    ProverRwQueryNativeAttempt.native_attempt_exact]
  rfl

theorem retry_transport {C : Type} (entropy : Entropy C) (pub : Pub) (compiled : Compiled)
    (variant : transport.Variant) (h : Hash) (store : Store) (callback : C)
    (k : Usize) (n : Nat) (bound : k.val+n=8) :
    mapR sourceOutput (prover.retry_attempt entropy pub compiled variant h store callback k) =
      mapR drop (ProverCommitRetry34.run (queryAttempt entropy pub compiled variant h) n k.val (callback,store)) := by
  rw [←attempt_transport]
  exact ProverRwRetryModel.retry entropy pub compiled variant h store callback k n bound

omit [ExternalFuns] in
theorem admitted_eight (ops : ExternalFuns) {C : Type} (entropy : Entropy C)
    (pub : Pub) (compiled : Compiled) (h : Hash) (store : Store) (callback : C) :
    letI : ExternalFuns := ProverRwCallerBinding.install ops
    mapR sourceOutput (prover.prove_masked_retrying_with entropy pub compiled .S2 h store callback) =
      mapR drop (ProverCommitRetry34.eight (queryAttempt entropy pub compiled .S2 h) (callback,store)) := by
  letI : ExternalFuns := ProverRwCallerBinding.install ops
  rw [←attempt_transport]
  exact ProverRwCallerBinding.eight ops entropy pub compiled h store callback

#print axioms attempt_transport
#print axioms retry_transport
#print axioms admitted_eight
end R1Z.ProverRwQueryRetry

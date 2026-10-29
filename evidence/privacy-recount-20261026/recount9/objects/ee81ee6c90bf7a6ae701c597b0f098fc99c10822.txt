import PV_DIAG9_Scope
set_option autoImplicit false
noncomputable section
namespace PV_DIAG10
open Aeneas Aeneas.Std Result R1Z ProverRwFull
variable [ExternalTypes] [ExternalFuns]
/-! Producers are explicit complete outer Results, including returned errors.
Entropy's success continuation requires the actual masked-attempt cone.
Neither op227 nonvacuity nor a postcondition supplies that producer. -/
def PV_DIAG10_Link_Entropy {C : Type} (entropy : ProverRwRetryModel.Entropy C) : Prop :=
 ∀ k c, ∃ out, entropy.call_mut c (ProverCommitRetrySource34.word k)=.ok out
def PV_DIAG10_Link_MaskedAttempt (pub : ProverRwRetryModel.Pub)
 (compiled : ProverRwRetryModel.Compiled) (variant : transport.Variant)
 (hash : ProverRwRetryModel.Hash) : Prop :=
 ∀ secret store, ∃ out, prover.prove_masked_attempt pub compiled variant hash secret store=.ok out
theorem attempt_from_complete_producers {C : Type}
 (entropy : ProverRwRetryModel.Entropy C) (pub : ProverRwRetryModel.Pub)
 (compiled : ProverRwRetryModel.Compiled) (variant : transport.Variant)
 (hash : ProverRwRetryModel.Hash) (he : PV_DIAG10_Link_Entropy entropy)
 (hm : PV_DIAG10_Link_MaskedAttempt pub compiled variant hash)
 (k : Nat) (s : C × ProverRwRetryModel.Store) :
 ∃ out, ProverRwRetryModel.attempt entropy pub compiled variant hash k s=.ok out := by
 obtain ⟨⟨status,after⟩,hs⟩ := he k s.1
 unfold ProverRwRetryModel.attempt
 rw [hs]
 cases status with
 | Err e => exact ⟨_,rfl⟩
 | Ok secret =>
   obtain ⟨⟨status,store⟩,hm⟩ := hm secret s.2
   change ∃ out, (prover.prove_masked_attempt pub compiled variant hash secret s.2 >>= _) = .ok out
   rw [hm]
   cases status with
   | Ok proof => exact ⟨_,rfl⟩
   | Err e => cases e <;> exact ⟨_,rfl⟩
#print axioms attempt_from_complete_producers
theorem retry_from_complete_producers {C : Type}
 (entropy : ProverRwRetryModel.Entropy C) (pub : ProverRwRetryModel.Pub)
 (compiled : ProverRwRetryModel.Compiled) (variant : transport.Variant)
 (hash : ProverRwRetryModel.Hash) (he : PV_DIAG10_Link_Entropy entropy)
 (hm : PV_DIAG10_Link_MaskedAttempt pub compiled variant hash)
 (store : ProverRwRetryModel.Store) (callback : C) (k : Usize) (n : Nat)
 (bound : k.val+n=8) :
 prover.retry_attempt entropy pub compiled variant hash store callback k ≠ .fail .panic :=
 PV_DIAG9.extracted_retry_no_panic entropy pub compiled variant hash store callback k n bound
   (attempt_from_complete_producers entropy pub compiled variant hash he hm)
#print axioms retry_from_complete_producers
theorem entropy_failure_bypasses_masked_cone {C : Type}
 (entropy : ProverRwRetryModel.Entropy C) (pub : ProverRwRetryModel.Pub)
 (compiled : ProverRwRetryModel.Compiled) (variant : transport.Variant)
 (hash : ProverRwRetryModel.Hash) (k : Nat) (s : C × ProverRwRetryModel.Store)
 (e : verifier.Error) (after : C)
 (he : entropy.call_mut s.1 (ProverCommitRetrySource34.word k)=.ok (.Err e,after)) :
 ProverRwRetryModel.attempt entropy pub compiled variant hash k s =
 .ok (.stop (ProverRwRetryModel.error e),(after,s.2)) := by
 unfold ProverRwRetryModel.attempt
 rw [he]
 rfl
#print axioms entropy_failure_bypasses_masked_cone
theorem entropy_panic_propagates {C : Type}
 (entropy : ProverRwRetryModel.Entropy C) (pub : ProverRwRetryModel.Pub)
 (compiled : ProverRwRetryModel.Compiled) (variant : transport.Variant)
 (hash : ProverRwRetryModel.Hash) (k : Nat) (s : C × ProverRwRetryModel.Store)
 (he : entropy.call_mut s.1 (ProverCommitRetrySource34.word k)=.fail .panic) :
 ProverRwRetryModel.attempt entropy pub compiled variant hash k s=.fail .panic := by
 unfold ProverRwRetryModel.attempt
 rw [he]
 rfl
#print axioms entropy_panic_propagates
theorem entropy_divergence_propagates {C : Type}
 (entropy : ProverRwRetryModel.Entropy C) (pub : ProverRwRetryModel.Pub)
 (compiled : ProverRwRetryModel.Compiled) (variant : transport.Variant)
 (hash : ProverRwRetryModel.Hash) (k : Nat) (s : C × ProverRwRetryModel.Store)
 (he : entropy.call_mut s.1 (ProverCommitRetrySource34.word k)=.div) :
 ProverRwRetryModel.attempt entropy pub compiled variant hash k s=.div := by
 unfold ProverRwRetryModel.attempt
 rw [he]
 rfl
#print axioms entropy_divergence_propagates
end PV_DIAG10

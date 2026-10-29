import PV_DIAG2_Rejection
set_option autoImplicit false
namespace PV_DIAG2
open Aeneas Aeneas.Std Result
open R1Z ProverCommitRetry34 ProverCommitSemanticTransport26
variable [ProverRwFull.ExternalTypes] [ProverRwFull.ExternalFuns]

/-- Result projection of the concrete client's generate(...).map_err(|_|
Error::Entropy) callback. The generate execution and account selection remain
opaque; failure and divergence are propagated. No effect-silence claim. -/
def clientEntropyStep {C E : Type}
    (generate : C → Usize → Result (core.result.Result ProverRwRetryModel.Secret E × C))
    (state : C) (k : Usize) :
 Result (core.result.Result ProverRwRetryModel.Secret ProverRwFull.verifier.Error × C) := do
   let (r,next) ← generate state k
   match r with
   | .Ok secret => ok (.Ok secret,next)
   | .Err _ => ok (.Err ProverRwFull.verifier.Error.Entropy,next)

def clientEntropy {C E : Type}
    (generate : C → Usize → Result (core.result.Result ProverRwRetryModel.Secret E × C)) :
 ProverRwRetryModel.Entropy C :=
 ⟨⟨fun state k => do let (r,_) ← clientEntropyStep generate state k; ok r⟩,
  clientEntropyStep generate⟩

theorem client_entropy_not_rejected {C E : Type}
    (generate : C → Usize → Result (core.result.Result ProverRwRetryModel.Secret E × C))
    (s after : C) (k : Usize) :
 (clientEntropy generate).call_mut s k ≠
   ok (.Err ProverRwFull.verifier.Error.Rejected,after) := by
 change clientEntropyStep generate s k ≠ _
 unfold clientEntropyStep
 cases h : generate s k with
 | fail e => simp
 | div => simp
 | ok pair => rcases pair with ⟨r,next⟩; cases r <;> simp

theorem client_attempt_reject_free {C E : Type}
    (generate : C → Usize → Result (core.result.Result ProverRwRetryModel.Secret E × C))
    (pub : ProverRwRetryModel.Pub) (compiled : ProverRwRetryModel.Compiled)
    (variant : ProverRwFull.transport.Variant) (hash : ProverRwRetryModel.Hash)
    (k : Nat) (state : C × ProverRwRetryModel.Store) :
 RejectFree (ProverRwRetryModel.attempt (clientEntropy generate) pub compiled variant hash k state) :=
 attempt_reject_free _ pub compiled variant hash k state
   (fun after => client_entropy_not_rejected generate state.1 after _)

theorem client_run_reject_free {C E : Type}
    (generate : C → Usize → Result (core.result.Result ProverRwRetryModel.Secret E × C))
    (pub : ProverRwRetryModel.Pub) (compiled : ProverRwRetryModel.Compiled)
    (variant : ProverRwFull.transport.Variant) (hash : ProverRwRetryModel.Hash)
    (n k : Nat) (state : C × ProverRwRetryModel.Store) :
 RejectFree (run (ProverRwRetryModel.attempt (clientEntropy generate) pub compiled variant hash) n k state) :=
 run_reject_free _ (client_attempt_reject_free generate pub compiled variant hash) n k state

/-- Full actual retry Result, not the old count-erasing publication view.
The error occurrence excluded here is final Rejected, not exhaustion. -/
theorem source_client_no_rejected {C E : Type}
    (generate : C → Usize → Result (core.result.Result ProverRwRetryModel.Secret E × C))
    (pub : ProverRwRetryModel.Pub) (compiled : ProverRwRetryModel.Compiled)
    (variant : ProverRwFull.transport.Variant) (hash : ProverRwRetryModel.Hash)
    (store after : ProverRwRetryModel.Store) (state : C) (k : Usize) (n : Nat)
    (bound : k.val+n=8) :
 ProverRwFull.prover.retry_attempt (clientEntropy generate) pub compiled variant hash store state k ≠
   ok (.Err ProverRwFull.verifier.Error.Rejected,after) := by
 intro bad
 have law := ProverRwRetryModel.retry (clientEntropy generate) pub compiled variant hash store state k n bound
 rw [bad] at law
 simp only [mapR,ProverRwRetryModel.sourceOutput,ProverRwRetryModel.error] at law
 have free := client_run_reject_free generate pub compiled variant hash n k.val (state,store)
 cases hrun : run (ProverRwRetryModel.attempt (clientEntropy generate) pub compiled variant hash) n k.val (state,store) with
 | fail e => simp [hrun,mapR] at law
 | div => simp [hrun,mapR] at law
 | ok pair =>
   rcases pair with ⟨step,next⟩
   cases step with
   | done p => simp [hrun,mapR,ProverRwRetryModel.drop] at law
   | retry => simp [hrun,mapR,ProverRwRetryModel.drop] at law
   | stop e =>
     have he : e = .Rejected := by
       have eq : .Rejected = e ∧ after = next.2 := by
         simpa [hrun,mapR,ProverRwRetryModel.drop,ProverRwRetryModel.sourceOutput,ProverRwRetryModel.error] using law
       exact eq.1.symm
     subst e
     exact free next hrun

#print axioms client_entropy_not_rejected
#print axioms client_attempt_reject_free
#print axioms client_run_reject_free
#print axioms source_client_no_rejected
end PV_DIAG2

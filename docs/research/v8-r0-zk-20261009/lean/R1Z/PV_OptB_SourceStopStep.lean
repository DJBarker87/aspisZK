import R1Z.PV_OptB_SourceEntropyStep
set_option autoImplicit false
namespace R1Z.PV_OptB_SourceStopStep
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
variable [ExternalTypes] [ExternalFuns]

/-- Every non-rejection body error exits before another OS callback. -/
theorem stopped {S : Type} (entropy : Entropy S) (pub : Pub) (compiled : Compiled)
    (hash : Hash) (store afterStore : Store) (state next : S) (secret : Secret)
    (k : Usize) (below : ¬ k >= prover.ATTEMPT_CAP) (e : verifier.Error) (nonretry : e ≠ .Rejected)
    (called : entropy.call_mut state k = .ok (.Ok secret,next))
    (body : prover.prove_masked_attempt pub compiled .S2 hash secret store =
      .ok (.Err e,afterStore)) :
    prover.retry_attempt entropy pub compiled .S2 hash store state k = .ok (.Err e,afterStore) := by
  rw [prover.retry_attempt]
  simp only [below,if_false,called,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.Insts.CoreOpsTry.branch,body]
  cases e <;> try rfl
  exact False.elim (nonretry rfl)

#print axioms stopped
end R1Z.PV_OptB_SourceStopStep

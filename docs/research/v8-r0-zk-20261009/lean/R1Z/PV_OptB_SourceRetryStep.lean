import R1Z.PV_OptB_SourceFirstFailure
set_option autoImplicit false
namespace R1Z.PV_OptB_SourceRetryStep
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
variable [ExternalTypes] [ExternalFuns]

/-- Exact recursive step of the extracted caller. The two premises describe
its actual callback and actual body, rather than replacement functions. -/
theorem rejected {S : Type} (entropy : Entropy S) (pub : Pub) (compiled : Compiled)
    (hash : Hash) (store afterStore : Store) (state next : S) (secret : Secret)
    (k : Usize) (below : ¬ k >= prover.ATTEMPT_CAP)
    (called : entropy.call_mut state k = .ok (.Ok secret,next))
    (body : prover.prove_masked_attempt pub compiled .S2 hash secret store =
      .ok (.Err .Rejected,afterStore)) :
    prover.retry_attempt entropy pub compiled .S2 hash store state k =
      prover.retry_attempt entropy pub compiled .S2 hash afterStore next (Usize.wrapping_add k 1#usize) := by
  rw [prover.retry_attempt]
  simp only [below,if_false,called,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.Insts.CoreOpsTry.branch,body,lift,bind_tc_ok]

#print axioms rejected
end R1Z.PV_OptB_SourceRetryStep

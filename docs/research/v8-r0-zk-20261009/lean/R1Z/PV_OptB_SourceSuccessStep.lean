import R1Z.PV_OptB_SourceRetryStep
set_option autoImplicit false
namespace R1Z.PV_OptB_SourceSuccessStep
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
variable [ExternalTypes] [ExternalFuns]

/-- Successful source-body execution stops before the next callback. -/
theorem succeeded {S : Type} (entropy : Entropy S) (pub : Pub) (compiled : Compiled)
    (hash : Hash) (store afterStore : Store) (state next : S) (secret : Secret)
    (k : Usize) (below : ¬ k >= prover.ATTEMPT_CAP) (proof : alloc.vec.Vec U8)
    (audit : prover.MaskedFixtureAudit)
    (called : entropy.call_mut state k = .ok (.Ok secret,next))
    (body : prover.prove_masked_attempt pub compiled .S2 hash secret store =
      .ok (.Ok (proof,audit),afterStore)) :
    prover.retry_attempt entropy pub compiled .S2 hash store state k =
      .ok (.Ok ⟨proof,audit,Usize.wrapping_add k 1#usize⟩,afterStore) := by
  rw [prover.retry_attempt]
  simp only [below,if_false,called,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.Insts.CoreOpsTry.branch,body,lift,bind_tc_ok]

#print axioms succeeded
end R1Z.PV_OptB_SourceSuccessStep

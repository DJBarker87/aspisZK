import R1Z.PV_OptB_SourceRetryStep
set_option autoImplicit false
namespace R1Z.PV_OptB_SourceEntropyStep
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
variable [ExternalTypes] [ExternalFuns]

/-- All exact callback errors stop the extracted recurrence at any entered
position, with the current durable store retained. -/
theorem callback_error {S : Type} (entropy : Entropy S) (pub : Pub) (compiled : Compiled)
    (hash : Hash) (store : Store) (state next : S) (e : verifier.Error)
    (k : Usize) (below : ¬ k >= prover.ATTEMPT_CAP)
    (called : entropy.call_mut state k = .ok (.Err e,next)) :
    prover.retry_attempt entropy pub compiled .S2 hash store state k =
      .ok (.Err e,store) := by
  rw [prover.retry_attempt]
  simp only [below,if_false,called,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

#print axioms callback_error
end R1Z.PV_OptB_SourceEntropyStep

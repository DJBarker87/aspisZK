import R1Z.PV_RE_AfterPrefix1000
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_AfterRejected10
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_AfterPrefix1000
variable [ExternalTypes] [ExternalFuns]

/-- A native reservation rejection returns before entropy dereference or
material construction in this exact source function. -/
theorem rejected {S : Type} (inst : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (secret : Secrets) (hash : Hash) (binding : Array U8 32#usize)
    (context : Context) (store store1 : S)
    (reply : inst.reserve store context.statement_digest context.mask_nonce = .ok (false,store1)) :
    ProverRwOuterAfterChecks.afterChecks inst secret hash binding context store =
      .ok (.Err aspis_prover.state_only_hiding.StateOnlyMaskBuildError.ReusedMaskNonce,store1) := by
  unfold ProverRwOuterAfterChecks.afterChecks
  rw [reply]
  rfl
#print axioms rejected
end R1Z.PV_RE_AfterRejected10

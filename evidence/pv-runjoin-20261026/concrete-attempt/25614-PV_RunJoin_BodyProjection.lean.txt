import R1Z.PV_RunJoin_GuardProjection
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BodyProjection
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
open ProverCommitSemanticTransport26 PV_RunJoin_ResultTransport
variable [ExternalTypes] [ExternalFuns]

theorem body (parametric : PV_RunJoin_StoreContinuationResidual.MapErrParametric)
    {S T : Type} (project : S → T)
    (left : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (right : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T)
    (pub : Pub) (compiled : Compiled) (variant : transport.Variant) (hash : Hash)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (binding : Array U8 32#usize) (secret : Secret) (s : S)
    (callback : mapR (fun out => (out.1,project out.2))
      (left.«reserve» s context.statement_digest context.mask_nonce) =
      right.«reserve» (project s) context.statement_digest context.mask_nonce) :
    mapR (fun out => (out.1,project out.2))
      (prover.prove_masked_with_attempt left pub compiled variant hash context binding secret s) =
    prover.prove_masked_with_attempt right pub compiled variant hash context binding secret (project s) := by
  rw [ProverRwBodyStore.factor,ProverRwBodyStore.factor]
  rw [← PV_RunJoin_ReservationGuards.source_eq,
      ← PV_RunJoin_ReservationGuards.source_eq]
  have reservation := PV_RunJoin_GuardProjection.guarded project left right secret hash binding context s callback
  rw [← reservation]
  apply PV_RunJoin_ResultTransport.bind_map
  intro pair
  rcases pair with ⟨status,after⟩
  dsimp only [Aeneas.Std.uncurry]
  exact PV_RunJoin_ContinuationProjection.after_reserve parametric project left right
    pub compiled variant hash context binding secret status after

#print axioms body
end R1Z.PV_RunJoin_BodyProjection

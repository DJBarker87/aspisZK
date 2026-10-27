import R1Z.PV_RunJoin_ReservationProjection
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_GuardProjection
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
open ProverCommitSemanticTransport26 PV_RunJoin_BindCongruence
variable [ExternalTypes] [ExternalFuns]

theorem guarded {S T : Type} (project : S → T)
    (left : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (right : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T)
    (secret : Secret) (hash : Hash) (binding : Array U8 32#usize)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (s : S)
    (callback : mapR (fun out => (out.1,project out.2))
      (left.«reserve» s context.statement_digest context.mask_nonce) =
      right.«reserve» (project s) context.statement_digest context.mask_nonce) :
    mapR (fun out => (out.1,project out.2))
      (PV_RunJoin_ReservationGuards.guarded left secret hash binding context s) =
    PV_RunJoin_ReservationGuards.guarded right secret hash binding context (project s) := by
  unfold PV_RunJoin_ReservationGuards.guarded
  simp only [map_bind,map_if,map_ok]
  repeat' first
    | exact PV_RunJoin_ReservationProjection.after_checks project left right secret hash binding context s callback
    | rfl
    | apply bind_same
      intro value
      try simp only [map_bind,map_if,map_ok]
    | apply if_same

#print axioms guarded
end R1Z.PV_RunJoin_GuardProjection

import R1Z.PV_RunJoin_ReservationGuards
import R1Z.PV_RunJoin_Follows
import R1Z.PV_RunJoin_LedgerWorldFields
import R1Z.ProverRwBodyReservationTransport
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EnteredCallback
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
open PV_RunJoin_Follows PV_RunJoin_LedgerWorld
variable [ExternalTypes]

theorem entered (ops : ExternalFuns) (schedule : ProverCommitLedger36.Schedule)
    (unix : Bool) (address : Address) (secret : Secret) (hash : Hash)
    (binding : Array U8 32#usize)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (s : World) :
    letI : ExternalFuns := ops
    Follows (fun out : PV_RunJoin_ReservationGuards.MaterialStatus × World => out.2.entered) (.ok (some (address context.mask_nonce)))
      (ProverRwOuterAfterChecks.afterChecks (dictionary ops schedule unix address)
        secret hash binding context s) := by
  letI : ExternalFuns := ops
  intro out run
  have original := run
  unfold ProverRwOuterAfterChecks.afterChecks at run
  obtain ⟨⟨accepted,after⟩,called,_⟩ := PV_RunJoin_ResultPost.bind_eq_ok run
  have state := ProverRwBodyReservationTransport.callback_writeback
    (dictionary ops schedule unix address) secret hash binding context s after accepted called
  rw [original] at state
  change out.2 = after at state
  have entered := (PV_RunJoin_LedgerWorldFields.writeback ops schedule unix address s after
    context.statement_digest context.mask_nonce accepted called).2
  change .ok (some (address context.mask_nonce)) = (.ok out.2.entered : Result (Option ProverCommitLedger36.Path))
  rw [state,entered]

#print axioms entered
end R1Z.PV_RunJoin_EnteredCallback

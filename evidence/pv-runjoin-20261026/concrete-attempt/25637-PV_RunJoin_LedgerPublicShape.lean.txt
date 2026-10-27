import R1Z.PV_RunJoin_LedgerPublicEntry
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LedgerPublicShape
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
open PV_RunJoin_LedgerBody
variable [ExternalTypes] [ProverRwRngCaller.NativeTypes] [ProverRwRngCaller.ErasureFns]
variable {N C : Type}

theorem ledger_public (schedule : ProverCommitLedger36.Schedule) (unix : Bool)
    (address : PV_RunJoin_LedgerWorld.Address) (d : Inputs N C)
    (secret : Secret) (s next : State N C) (status : core.result.Result Proof verifier.Error)
    (run : body schedule unix address d secret s = .ok (status,next)) :
    next.ledger.model =
      match PV_RunJoin_PublicDecision.decision (d.ops s) address (d.pub s) .S2 (d.hash s) secret.mask_nonce with
      | none => s.ledger.model
      | some path => (ProverCommitLedger36.reserve schedule unix path s.ledger.model).2 := by
  have shape := native_ledger_shape schedule unix address d secret s next status run
  rw [PV_RunJoin_LedgerPublicEntry.reservation_eq schedule unix address d secret s next status run] at shape
  exact shape

#print axioms ledger_public
end R1Z.PV_RunJoin_LedgerPublicShape

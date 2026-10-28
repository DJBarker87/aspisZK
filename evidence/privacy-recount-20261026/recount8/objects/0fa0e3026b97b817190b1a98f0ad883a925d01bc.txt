import R1Z.PV_RunJoin_PublicDecision
import R1Z.PV_RunJoin_LedgerBody
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LedgerPublicEntry
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
open PV_RunJoin_LedgerBody ProverCommitSemanticTransport26
variable [ExternalTypes] [ProverRwRngCaller.NativeTypes] [ProverRwRngCaller.ErasureFns]
variable {N C : Type}

/-- Replace reconstruction from a full witness-dependent body RESULT by the
common public-prefix decision, on every returned source execution. A machine
failure/divergence returns no state and is not assigned an invented history. -/
theorem reservation_eq (schedule : ProverCommitLedger36.Schedule) (unix : Bool)
    (address : PV_RunJoin_LedgerWorld.Address) (d : Inputs N C)
    (secret : Secret) (s next : State N C) (status : core.result.Result Proof verifier.Error)
    (run : body schedule unix address d secret s = .ok (status,next)) :
    reservation schedule unix address d secret s =
      PV_RunJoin_PublicDecision.decision (d.ops s) address (d.pub s) .S2 (d.hash s) secret.mask_nonce := by
  have original := run
  unfold body mapR at run
  obtain ⟨raw,called,tail⟩ := PV_RunJoin_ResultPost.bind_eq_ok run
  have decided := PV_RunJoin_PublicDecision.returned (d.ops s) schedule unix address
    (d.pub s) (d.compiled s) .S2 secret (d.hash s)
    (PV_RunJoin_LedgerWorldInvariant.clear s.ledger) raw.2 raw.1 rfl called
  have state := congrArg (fun pair => pair.2.ledger) (Result.ok.inj tail)
  dsimp only at state
  unfold reservation
  rw [original]
  change next.ledger.entered = _
  rw [← state]
  exact decided.symm

#print axioms reservation_eq
end R1Z.PV_RunJoin_LedgerPublicEntry

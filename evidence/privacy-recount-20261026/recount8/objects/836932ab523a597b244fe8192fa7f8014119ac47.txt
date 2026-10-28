import R1Z.PV_RunJoin_LedgerBody
import R1Z.PV_RunJoin_LedgerStrict
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LedgerBodyStrict
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
open PV_RunJoin_LedgerBody
variable [ExternalTypes] [ProverRwRngCaller.NativeTypes] [ProverRwRngCaller.ErasureFns]
variable {N C : Type}

/-- Entry, including duplicate/error outcomes, is observable in the modeled
history. This implication does not identify that model with native IO. -/
theorem entered_strict (schedule : ProverCommitLedger36.Schedule) (unix : Bool)
    (address : PV_RunJoin_LedgerWorld.Address) (d : Inputs N C)
    (secret : Secret) (s next : State N C)
    (status : core.result.Result Proof verifier.Error) (path : ProverCommitLedger36.Path)
    (run : body schedule unix address d secret s = .ok (status,next))
    (entered : reservation schedule unix address d secret s = some path) :
    s.ledger.model.history.length < next.ledger.model.history.length := by
  have shape := native_ledger_shape schedule unix address d secret s next status run
  rw [entered] at shape
  rw [shape]
  exact PV_RunJoin_LedgerStrict.reserve_history_strict schedule unix path s.ledger.model

/-- Exact characterization useful for the remaining public-entry field. A
per-witness reconstruction from the body result is not a common boundary. -/
theorem no_entry_iff_unchanged (schedule : ProverCommitLedger36.Schedule) (unix : Bool)
    (address : PV_RunJoin_LedgerWorld.Address) (d : Inputs N C)
    (secret : Secret) (s next : State N C)
    (status : core.result.Result Proof verifier.Error)
    (run : body schedule unix address d secret s = .ok (status,next)) :
    reservation schedule unix address d secret s = none ↔ next.ledger.model = s.ledger.model := by
  constructor
  · intro entered
    have shape := native_ledger_shape schedule unix address d secret s next status run
    simpa only [entered] using shape
  · intro same
    cases entered : reservation schedule unix address d secret s with
    | none => rfl
    | some path =>
      have strict := entered_strict schedule unix address d secret s next status path run entered
      rw [same] at strict
      exact (Nat.lt_irrefl _ strict).elim

#print axioms entered_strict
#print axioms no_entry_iff_unchanged
end R1Z.PV_RunJoin_LedgerBodyStrict

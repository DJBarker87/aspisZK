import R1Z.PV_RunJoin_LedgerWorldInvariant
import R1Z.PV_RunJoin_UnifiedRetry
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LedgerBody
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
open PV_RunJoin_ResultPost ProverCommitSemanticTransport26
variable [ExternalTypes]
variable [ProverRwRngCaller.NativeTypes] [ProverRwRngCaller.ErasureFns]
variable {N C : Type}
abbrev State (N C : Type) := PV_RunJoin_UnifiedRetry.State N PV_RunJoin_LedgerWorld.World C

structure Inputs (N C : Type) where
  ops : State N C → ExternalFuns
  pub : State N C → Pub
  compiled : State N C → Compiled
  hash : State N C → Hash

/-- Actual generic emitted caller with explicit source-header/ledger-world
writeback. Native association of the modeled effects is still unproved.
This data construction is not installed at the deployed endpoint. -/
def body (schedule : ProverCommitLedger36.Schedule) (unix : Bool)
    (address : PV_RunJoin_LedgerWorld.Address) (d : Inputs N C) :
    PV_RunJoin_UnifiedRetry.Body (State N C) := fun secret s =>
  letI : ExternalFuns := d.ops s
  mapR (fun out => (out.1,{s with ledger := out.2}))
    (PV_RunJoin_GenericSourceCaller.caller
      (PV_RunJoin_LedgerWorld.dictionary (d.ops s) schedule unix address)
      (d.pub s) (d.compiled s) .S2 (d.hash s) secret (PV_RunJoin_LedgerWorldInvariant.clear s.ledger))

def reservation (schedule : ProverCommitLedger36.Schedule) (unix : Bool)
    (address : PV_RunJoin_LedgerWorld.Address) (d : Inputs N C)
    (secret : Secret) (s : State N C) : Option ProverCommitLedger36.Path :=
  match body schedule unix address d secret s with
  | .ok (_,after) => after.ledger.entered
  | .fail _ | .div => none

/-- Exact V337-shaped ledger equation for this candidate effect interpreter.
It is a model/control theorem; native IO/E2 and full source/header projection
are required before using this ledger as a deployed filesystem decoder. -/
theorem native_ledger_shape (schedule : ProverCommitLedger36.Schedule) (unix : Bool)
    (address : PV_RunJoin_LedgerWorld.Address) (d : Inputs N C)
    (secret : Secret) (s next : State N C)
    (status : core.result.Result Proof verifier.Error)
    (run : body schedule unix address d secret s = .ok (status,next)) :
    next.ledger.model =
      match reservation schedule unix address d secret s with
      | none => s.ledger.model
      | some path => (ProverCommitLedger36.reserve schedule unix path s.ledger.model).2 := by
  have original := run
  unfold body mapR at run
  obtain ⟨raw,computation,run⟩ := bind_eq_ok run
  have invariant := PV_RunJoin_LedgerWorldInvariant.caller (d.ops s) schedule unix address s.ledger
    (d.pub s) (d.compiled s) .S2 (d.hash s) secret raw computation
  have same := congrArg (fun pair => pair.2.ledger) (Result.ok.inj run)
  dsimp only at same invariant
  rw [same] at invariant
  unfold reservation
  rw [original]
  cases entered : next.ledger.entered <;>
    simpa only [PV_RunJoin_LedgerWorldInvariant.Invariant,entered] using invariant

#print axioms native_ledger_shape
end R1Z.PV_RunJoin_LedgerBody

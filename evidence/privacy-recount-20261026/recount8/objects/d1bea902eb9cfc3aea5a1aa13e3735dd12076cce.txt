import R1Z.ProverRwP6BodyStore
import R1Z.PV_RunJoin_LedgerSourceBody
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_StoreLedgerSource
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
variable [ExternalTypes] [ProverRwRngCaller.NativeTypes] [ProverRwRngCaller.ErasureFns]

def inputs {N C : Type} (ops : PV_RunJoin_LedgerBody.State N C → ExternalFuns)
    (pub : PV_RunJoin_LedgerBody.State N C → Pub)
    (compiled : PV_RunJoin_LedgerBody.State N C → Compiled)
    (hash : PV_RunJoin_LedgerBody.State N C → Hash) : PV_RunJoin_LedgerBody.Inputs N C :=
  ⟨fun s => ProverRwP6BodyStore.selected (ops s),pub,compiled,hash⟩

/-- The P6 selected dictionary inhabits the explicit ledger interpreter.
Native filesystem/effect association and fixture byte models remain obligations. -/
theorem body_source {N C : Type} (ops : PV_RunJoin_LedgerBody.State N C → ExternalFuns)
    (pub : PV_RunJoin_LedgerBody.State N C → Pub)
    (compiled : PV_RunJoin_LedgerBody.State N C → Compiled)
    (hash : PV_RunJoin_LedgerBody.State N C → Hash)
    (schedule : ProverCommitLedger36.Schedule) (unix : Bool)
    (address : PV_RunJoin_LedgerWorld.Address) :
    PV_RunJoin_UnifiedRetry.BodySourceLaw
      (PV_RunJoin_LedgerSourceBody.sourceBody (inputs ops pub compiled hash))
      (PV_RunJoin_LedgerBody.body schedule unix address (inputs ops pub compiled hash)) := by
  apply PV_RunJoin_LedgerSourceBody.source_law
  intro s
  rfl
#print axioms inputs
#print axioms body_source
end R1Z.PV_Join_StoreLedgerSource

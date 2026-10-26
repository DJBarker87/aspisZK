import R1Z.PV_Join_PublicCaller
import R1Z.PV_RunJoin_LedgerSourceBody
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_LedgerSource
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
variable [ProverRwRngCaller.NativeTypes] [ProverRwRngCaller.ErasureFns]

abbrev World (N C : Type) := PV_RunJoin_LedgerBody.State N C

def inputs (base : ExternalTypes) {N C : Type}
    (ops : World N C → @ExternalFuns (PV_Join_PublicCaller.native base)) :
    letI : ExternalTypes := PV_Join_PublicCaller.native base
    (World N C → Pub) → (World N C → Compiled) → (World N C → Hash) →
      PV_RunJoin_LedgerBody.Inputs N C := by
  letI : ExternalTypes := PV_Join_PublicCaller.native base
  intro pub compiled hash
  exact ⟨fun s => PV_Join_PublicCaller.selected base (ops s),pub,compiled,hash⟩

/-- The selected source-law caller also inhabits the explicit ledger-world
body. This projects the complete source Result and store header, with native
filesystem/oracle association and independent model bytes still separate. -/
theorem body_source (base : ExternalTypes) {N C : Type}
    (ops : World N C → @ExternalFuns (PV_Join_PublicCaller.native base)) :
    letI : ExternalTypes := PV_Join_PublicCaller.native base
    ∀ (pub : World N C → Pub) (compiled : World N C → Compiled) (hash : World N C → Hash)
    (schedule : ProverCommitLedger36.Schedule) (unix : Bool) (address : PV_RunJoin_LedgerWorld.Address),
    PV_RunJoin_UnifiedRetry.BodySourceLaw
      (PV_RunJoin_LedgerSourceBody.sourceBody (inputs base ops pub compiled hash))
      (PV_RunJoin_LedgerBody.body schedule unix address (inputs base ops pub compiled hash)) := by
  letI : ExternalTypes := PV_Join_PublicCaller.native base
  intro pub compiled hash schedule unix address
  apply PV_RunJoin_LedgerSourceBody.source_law
  intro s
  rfl

#print axioms inputs
#print axioms body_source
end R1Z.PV_Join_LedgerSource

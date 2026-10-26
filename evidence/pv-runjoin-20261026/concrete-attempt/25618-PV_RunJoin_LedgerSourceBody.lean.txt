import R1Z.PV_RunJoin_LedgerSourceProjection
import R1Z.PV_RunJoin_LedgerBody
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LedgerSourceBody
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
open ProverCommitSemanticTransport26 PV_RunJoin_LedgerBody
variable [ExternalTypes] [ProverRwRngCaller.NativeTypes] [ProverRwRngCaller.ErasureFns]
variable {N C : Type}

def sourceBody (d : Inputs N C) : PV_RunJoin_UnifiedRetry.SourceBody (State N C) :=
  ⟨d.ops,d.pub,d.compiled,d.hash,fun s => s.ledger.header⟩

theorem source_law (schedule : ProverCommitLedger36.Schedule) (unix : Bool)
    (address : PV_RunJoin_LedgerWorld.Address) (d : Inputs N C)
    (identity : ∀ s, PV_RunJoin_MapErrInstalled.Identity (d.ops s)) :
    PV_RunJoin_UnifiedRetry.BodySourceLaw (sourceBody d)
      (body schedule unix address d) := by
  intro s secret
  change mapR (fun out : core.result.Result Proof verifier.Error × State N C => (out.1,out.2.ledger.header))
    (mapR (fun out : core.result.Result Proof verifier.Error × PV_RunJoin_LedgerWorld.World => (out.1,{s with ledger := out.2})) _) = _
  rw [PV_RunJoin_ResultTransport.map_comp]
  exact PV_RunJoin_LedgerSourceProjection.caller (d.ops s) (identity s)
    schedule unix address (d.pub s) (d.compiled s) .S2 (d.hash s) secret
    (PV_RunJoin_LedgerWorldInvariant.clear s.ledger)

/-- Source body changes only the ledger world; entropy and client cursors
retain their exact values, including returned errors. -/
theorem provider_frame (schedule : ProverCommitLedger36.Schedule) (unix : Bool)
    (address : PV_RunJoin_LedgerWorld.Address) (d : Inputs N C)
    (secret : Secret) (s next : State N C) (status : core.result.Result Proof verifier.Error)
    (run : body schedule unix address d secret s = .ok (status,next)) :
    next.provider = s.provider := by
  unfold body mapR at run
  obtain ⟨out,_,same⟩ := PV_RunJoin_ResultPost.bind_eq_ok run
  exact congrArg (fun pair => pair.2.provider) (Result.ok.inj same).symm

#print axioms source_law
#print axioms provider_frame
end R1Z.PV_RunJoin_LedgerSourceBody

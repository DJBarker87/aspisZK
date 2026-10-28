import R1Z.PV_RunJoin_NativeSelectedInputs
set_option autoImplicit false
namespace R1Z.PV_RunJoin_LedgerFrame32
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel ProverCommitSemanticTransport26
open PV_RunJoin_LedgerBody
variable [ExternalTypes] [ProverRwRngCaller.NativeTypes] [ProverRwRngCaller.ErasureFns]
variable {N C : Type}

/-- Exact complete returned-world frame for the selected source body. Both
inner success and inner errors retain the original provider, nonce policy
and client state; the one returned ledger world is written back. -/
theorem returned (schedule : ProverCommitLedger36.Schedule) (unix : Bool)
    (address : PV_RunJoin_LedgerWorld.Address) (d : Inputs N C)
    (secret : Secret) (s next : State N C)
    (status : core.result.Result Proof verifier.Error)
    (h : body schedule unix address d secret s = .ok (status,next)) :
    next={s with ledger := next.ledger} := by
  unfold body mapR at h
  obtain ⟨out,_,same⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
  have hs := congrArg (fun pair => pair.2) (Result.ok.inj same)
  exact hs.symm.trans (congrArg (fun l => {s with ledger := l})
    (congrArg (fun t => t.ledger) hs))
#print axioms returned

theorem coordinates (schedule : ProverCommitLedger36.Schedule) (unix : Bool)
    (address : PV_RunJoin_LedgerWorld.Address) (d : Inputs N C)
    (secret : Secret) (s next : State N C)
    (status : core.result.Result Proof verifier.Error)
    (h : body schedule unix address d secret s = .ok (status,next)) :
    next.provider=s.provider ∧ next.policy=s.policy ∧ next.client=s.client := by
  have hf := returned schedule unix address d secret s next status h
  exact ⟨congrArg (fun t => t.provider) hf,congrArg (fun t => t.policy) hf,
    congrArg (fun t => t.client) hf⟩
#print axioms coordinates
end R1Z.PV_RunJoin_LedgerFrame32

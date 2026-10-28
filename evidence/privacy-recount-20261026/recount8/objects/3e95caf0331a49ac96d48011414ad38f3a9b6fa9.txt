import R1Z.PV_RunJoin_LedgerBody
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LedgerBodyFrames
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
open PV_RunJoin_ResultPost PV_RunJoin_LedgerBody ProverCommitSemanticTransport26
variable [ExternalTypes] [ProverRwRngCaller.NativeTypes] [ProverRwRngCaller.ErasureFns]
variable {N C : Type}

/-- The candidate source body writes back only its effect carrier. This says
nothing about the adequacy of that carrier for the native filesystem. -/
theorem frames (schedule : ProverCommitLedger36.Schedule) (unix : Bool)
    (address : PV_RunJoin_LedgerWorld.Address) (d : Inputs N C)
    (secret : Secret) (s next : State N C)
    (status : core.result.Result Proof verifier.Error)
    (run : body schedule unix address d secret s = .ok (status,next)) :
    next.provider = s.provider ∧ next.policy = s.policy ∧ next.client = s.client := by
  unfold body mapR at run
  obtain ⟨raw,computation,run⟩ := bind_eq_ok run
  have state := congrArg Prod.snd (Result.ok.inj run)
  exact ⟨congrArg (fun s => s.provider) state.symm,
    congrArg (fun s => s.policy) state.symm,
    congrArg (fun s => s.client) state.symm⟩

#print axioms frames
end R1Z.PV_RunJoin_LedgerBodyFrames

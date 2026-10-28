import R1Z.PV_RunJoin_EnteredGuards
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EnteredBody
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
open PV_RunJoin_Follows PV_RunJoin_LedgerWorld
variable [ExternalTypes]

theorem body (ops : ExternalFuns) (schedule : ProverCommitLedger36.Schedule)
    (unix : Bool) (address : Address) (pub : Pub) (compiled : Compiled)
    (variant : transport.Variant) (secret : Secret) (hash : Hash)
    (binding : Array U8 32#usize)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (s : World)
    (empty : s.entered = none) :
    letI : ExternalFuns := ops
    Follows (fun out : core.result.Result Proof verifier.Error × World => out.2.entered)
      (PV_RunJoin_PublicReservation.guards address secret.mask_nonce context)
      (prover.prove_masked_with_attempt (dictionary ops schedule unix address)
        pub compiled variant hash context binding secret s) := by
  letI : ExternalFuns := ops
  rw [ProverRwBodyStore.factor]
  apply continuation (fun out : PV_RunJoin_ReservationGuards.MaterialStatus × World => out.2.entered)
  · rw [← PV_RunJoin_ReservationGuards.source_eq]
    exact PV_RunJoin_EnteredGuards.guarded ops schedule unix address secret hash binding context s empty
  · intro pair out run
    rcases pair with ⟨status,after⟩
    have state := ProverRwBodyStore.continuation (dictionary ops schedule unix address)
      pub compiled variant hash context binding secret status after
    change ProverRwBodyStoreSource.afterReserve (dictionary ops schedule unix address)
      pub compiled variant hash context binding secret status after = .ok out at run
    rw [run] at state
    change out.2 = after at state
    exact congrArg (fun world => world.entered) state

#print axioms body
end R1Z.PV_RunJoin_EnteredBody

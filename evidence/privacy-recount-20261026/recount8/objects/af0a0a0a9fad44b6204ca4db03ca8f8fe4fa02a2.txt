import R1Z.ProverRwFullFuns
import R1Z.PV_RunJoin_ResultPost
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ReserveStoreFrame
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_ResultPost
variable [ExternalTypes] [ExternalFuns]
abbrev Store := aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore

/-- The full emitted fallible reservation returns only the same directory
handle with last_error reset. Native file creation/writes are external effects;
they are not encoded in this returned source record. No IO reply is assumed. -/
theorem fallible_store (self : Store) (statement nonce : Array U8 32#usize) :
    Post (fun out => out.2 = {self with last_error := none})
      (aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible self statement nonce) := by
  intro out run
  unfold aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible at run
  repeat' first
    | exact congrArg Prod.snd (Result.ok.inj run).symm
    | obtain ⟨_,_,run⟩ := bind_eq_ok run
      try dsimp only at run
    | split at run

#print axioms fallible_store
end R1Z.PV_RunJoin_ReserveStoreFrame

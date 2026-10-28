import R1Z.PV_RunJoin_ReserveStoreFrame
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ReserveHandleFields
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_ResultPost PV_RunJoin_ReserveStoreFrame
variable [ExternalTypes] [ExternalFuns]

theorem fallible_directory (self after : Store) (statement nonce : Array U8 32#usize)
    (status : core.result.Result Bool std.io.error.Error)
    (run : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
      self statement nonce = .ok (status,after)) : after.directory = self.directory :=
  congrArg (fun store => store.directory) (fallible_store self statement nonce (status,after) run)

theorem fallible_last_error (self after : Store) (statement nonce : Array U8 32#usize)
    (status : core.result.Result Bool std.io.error.Error)
    (run : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
      self statement nonce = .ok (status,after)) : after.last_error = none :=
  congrArg (fun store => store.last_error) (fallible_store self statement nonce (status,after) run)

theorem reset_eq (self : Store) (clear : self.last_error = none) :
    ({self with last_error := none} : Store) = self := by
  cases self with
  | mk directory last_error => cases clear; rfl

theorem fallible_same_handle (self after : Store) (statement nonce : Array U8 32#usize)
    (status : core.result.Result Bool std.io.error.Error)
    (clear : self.last_error = none)
    (run : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
      self statement nonce = .ok (status,after)) : after = self :=
  (fallible_store self statement nonce (status,after) run).trans (reset_eq self clear)

#print axioms fallible_directory
#print axioms fallible_last_error
#print axioms reset_eq
#print axioms fallible_same_handle
end R1Z.PV_RunJoin_ReserveHandleFields

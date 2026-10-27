import R1Z.PDict_OwnedErrorTransport
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_ReserveFailure
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_OwnedErrorObservation
variable [ExternalTypes]

theorem source_failure (ops : ExternalFuns) (s : Store) (sd nonce : Array U8 32#usize)
    (e : Aeneas.Std.Error) (h : @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible _ ops s sd nonce = .fail e) :
    @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve _ ops s sd nonce = .fail e := by
  rw [PDict_OwnedErrorTransport.source_factor, h]
  rfl

theorem source_divergence (ops : ExternalFuns) (s : Store) (sd nonce : Array U8 32#usize)
    (h : @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible _ ops s sd nonce = .div) :
    @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve _ ops s sd nonce = .div := by
  rw [PDict_OwnedErrorTransport.source_factor, h]
  rfl

theorem kind_failure (ops : ExternalFuns) (s s' : Store) (sd nonce : Array U8 32#usize)
    (e : std.io.error.Error) (failure : Aeneas.Std.Error)
    (hr : @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible _ ops s sd nonce = .ok (.Err e,s'))
    (hk : @std.io.error.Error.kind _ ops e = .fail failure) :
    @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve _ ops s sd nonce = .fail failure := by
  rw [PDict_OwnedErrorTransport.source_factor,hr]
  change (do let k ← @std.io.error.Error.kind _ ops e
             .ok (false,{s' with last_error := some k})) = _
  rw [hk]
  rfl

theorem kind_divergence (ops : ExternalFuns) (s s' : Store) (sd nonce : Array U8 32#usize)
    (e : std.io.error.Error)
    (hr : @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible _ ops s sd nonce = .ok (.Err e,s'))
    (hk : @std.io.error.Error.kind _ ops e = .div) :
    @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve _ ops s sd nonce = .div := by
  rw [PDict_OwnedErrorTransport.source_factor,hr]
  change (do let k ← @std.io.error.Error.kind _ ops e
             .ok (false,{s' with last_error := some k})) = _
  rw [hk]
  rfl

#print axioms source_failure
#print axioms source_divergence
#print axioms kind_failure
#print axioms kind_divergence
end R1Z.PDict_ReserveFailure

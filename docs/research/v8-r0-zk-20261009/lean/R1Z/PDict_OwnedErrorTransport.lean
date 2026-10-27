import R1Z.PDict_OwnedErrorObservation
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_OwnedErrorTransport
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_OwnedErrorObservation
variable [ExternalTypes]
def finish (ops : ExternalFuns)
    (r : core.result.Result Bool std.io.error.Error) (s : Store) : Result (Bool × Store) :=
  match r with
  | .Ok b => .ok (b,s)
  | .Err e => do
    let k ← @std.io.error.Error.kind _ ops e
    .ok (false,{s with last_error := some k})
def finishOwned (r : core.result.Result Bool Kind) (s : Store) : Bool × Store :=
  match r with
  | .Ok b => (b,s)
  | .Err k => (false,{s with last_error := some k})

theorem source_factor (ops : ExternalFuns) (s : Store) (sd nonce : Array U8 32#usize) :
    @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve _ ops s sd nonce =
    (do
      let (r,s') ← @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible _ ops s sd nonce
      finish ops r s') := rfl

/-- All dynamic payloads are universally quantified here. The missing native
kind equation stays explicit rather than becoming an error representation axiom. -/
theorem finish_transport (ops : ExternalFuns) (kind : std.io.error.Error → Kind)
    (hkind : ∀ e, @std.io.error.Error.kind _ ops e = .ok (kind e))
    (r : core.result.Result Bool std.io.error.Error) (s : Store) :
    finish ops r s = .ok (finishOwned (owned kind r) s) := by
  cases r with
  | Ok b => rfl
  | Err e =>
    change (do let k ← @std.io.error.Error.kind _ ops e
               .ok (false,{s with last_error := some k})) = _
    rw [hkind]
    rfl

theorem reserve_transport (ops : ExternalFuns) (kind : std.io.error.Error → Kind)
    (hkind : ∀ e, @std.io.error.Error.kind _ ops e = .ok (kind e))
    (s : Store) (sd nonce : Array U8 32#usize) :
    @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve _ ops s sd nonce =
    (do
      let (r,s') ← @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible _ ops s sd nonce
      .ok (finishOwned (owned kind r) s')) := by
  rw [source_factor]
  congr 1
  funext rs
  exact finish_transport ops kind hkind rs.1 rs.2

#print axioms source_factor
#print axioms finish_transport
#print axioms reserve_transport
end R1Z.PDict_OwnedErrorTransport

import R1Z.PDict_OwnedErrorTransport
import R1Z.PDict_RejectionStd
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_OwnedErrorDictionary
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_OwnedErrorObservation PDict_OwnedErrorTransport
/-- Reference-only dictionary. This is not a native representation of arbitrary
std::io::Error: the native kind quotient and all OS/world adequacy remain open. -/
@[reducible] def types (base : ExternalTypes) : ExternalTypes :=
  PDict_RejectionStd.native {base with op3 := core.io.error.ErrorKind}
@[reducible] def selected (base : ExternalTypes) (ops : @ExternalFuns (types base)) :
    @ExternalFuns (types base) :=
  letI : ExternalTypes := types base
  { PDict_RejectionStd.selected {base with op3 := core.io.error.ErrorKind} ops with
    op23 := fun e => .ok e }

theorem reference_type3 (base : ExternalTypes) : (types base).op3 = core.io.error.ErrorKind := rfl

theorem reference_kind (base : ExternalTypes) (ops : @ExternalFuns (types base))
    (e : core.io.error.ErrorKind) : (selected base ops).op23 e = .ok e := rfl

/-- The source reserve continuation can run on the owned reference dictionary
without any error-kind equation as a premise. Native-to-reference is not claimed. -/
theorem reserve_reference (base : ExternalTypes) (ops : @ExternalFuns (types base))
    (s : @Store (types base)) (sd nonce : Array U8 32#usize) :
    @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
      (types base) (selected base ops) s sd nonce =
    (do
      let (r,s') ← @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
        (types base) (selected base ops) s sd nonce
      .ok (@finishOwned (types base) (@owned (types base) id r) s')) :=
  @reserve_transport (types base) (selected base ops) id (fun _ => rfl) s sd nonce

#print axioms reference_type3
#print axioms reference_kind
#print axioms reserve_reference
end R1Z.PDict_OwnedErrorDictionary

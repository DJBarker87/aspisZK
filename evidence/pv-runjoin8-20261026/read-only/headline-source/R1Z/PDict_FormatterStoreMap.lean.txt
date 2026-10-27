import R1Z.PDict_FormatterTransport1
import R1Z.PDict_OwnedErrorTransport
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FormatterStoreMap
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
abbrev Store := @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore

def store (b : ExternalTypes) (F : Type) (s : @Store b) : @Store (types b F) :=
  @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.mk (types b F)
    (@aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.directory b s)
    (@aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.last_error b s)
def unstore (b : ExternalTypes) (F : Type) (s : @Store (types b F)) : @Store b :=
  @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.mk b
    (@aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.directory (types b F) s)
    (@aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.last_error (types b F) s)

theorem store_roundtrip (b : ExternalTypes) (F : Type) (s : @Store b) :
    unstore b F (store b F s) = s := by cases s; rfl

def pairStore (b : ExternalTypes) (F : Type) {A : Type} (x : A × @Store b) : A × @Store (types b F) :=
  (x.1, store b F x.2)

/-- Source wrapper transport. Only the fallible-run transport is a premise;
Error.kind is retained by the typed dictionary map, not postulated anew. -/
theorem reserve (b : ExternalTypes) (F : Type) (ops : @ExternalFuns b)
    (s : @Store b) (sd nonce : Array U8 32#usize)
    (h : @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
        (types b F) (selected b F ops) (store b F s) sd nonce =
      resultMap (pairStore b F) (@aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible b ops s sd nonce)) :
    @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
        (types b F) (selected b F ops) (store b F s) sd nonce =
      resultMap (pairStore b F) (@aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve b ops s sd nonce) := by
  unfold aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
  rw [h]
  cases hr : @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible b ops s sd nonce with
  | fail e => rfl
  | div => rfl
  | ok rs =>
    rcases rs with ⟨r,s'⟩
    cases r with
    | Ok value => rfl
    | Err e =>
      change (do
        let k ← @std.io.error.Error.kind b ops e
        .ok (false, store b F {s' with last_error := some k})) =
        resultMap (pairStore b F) (do
          let k ← @std.io.error.Error.kind b ops e
          .ok (false,{s' with last_error := some k}))
      cases @std.io.error.Error.kind b ops e <;> rfl

#print axioms store_roundtrip
#print axioms reserve
end R1Z.PDict_FormatterStoreMap

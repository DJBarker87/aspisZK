import R1Z.PDict_FallibleTransport
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_StoreTransport
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap PDict_FormatterStoreMap

/-- Complete source reserve transport, including false/error, machine failure and divergence.
No fallible-run hypothesis remains. Native File/Error world association is separate. -/
theorem reserve (b : ExternalTypes) (F : Type) (ops : @ExternalFuns b)
    (s : @Store b) (sd nonce : Array U8 32#usize) :
    @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
        (types b F) (selected b F ops) (store b F s) sd nonce =
      resultMap (pairStore b F) (@aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve b ops s sd nonce) :=
  PDict_FormatterStoreMap.reserve b F ops s sd nonce (PDict_FallibleTransport.fallible b F ops s sd nonce)
#print axioms reserve
end R1Z.PDict_StoreTransport

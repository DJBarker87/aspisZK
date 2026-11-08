import NNQ_ObserverHelpers
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNQ_HostDigest
open Aeneas Aeneas.Std Result
variable (S : AdapterRw.Ops)
    (o : AdapterRw.SolanaDigest → Slice (Slice U8) → Result (Array U8 32#usize))

theorem pubkey_op43 : AdapterRw.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey {S with op43 := o} =
    AdapterRw.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey S := rfl

theorem registry_op43 :
    AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry {S with op43 := o} =
    AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry S := by
  unfold AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry
  simp only [helper_0, helper_2, pubkey_op43]
#print axioms pubkey_op43
#print axioms registry_op43
end AspisR1.NNQ_HostDigest
end

import NMX_Emitted
set_option autoImplicit false
noncomputable section
namespace NMX_EmittedLinks
open Aeneas Aeneas.Std Result AdapterRw
/-- The actual fresh233 body, with same typed canonical carrier and explicit
217/234 child boundary, equals the coherent adopted body definitionally.
Only value/control transport; no owner/world/native packet is asserted here. -/
theorem adopted (ops : Ops) (p : solana_pubkey.Pubkey)
 (a : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey)
 (lane : U8) (slot : U64) :
 NMX_Emitted.auth ops ops.op50 (r1_pool_adapter.owned.authenticate_invariant_release_registry ops) p a pool lane slot =
 r1_pool_adapter.owned.authenticate_asq8_accounts ops p a pool lane slot := rfl
#print axioms adopted
end NMX_EmittedLinks
end

import NMX_R3_RegistryNativeParts
import NMX_R3_RegistryScalarOps
import NMX_R3_EntryRecordGuards
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryEntry1Check
open Aeneas Aeneas.Std AdapterRw
def check (ops : Ops) (v p : solana_pubkey.Pubkey) (e : r1_pool_adapter.owned.OwnedAccount) (t : U64) (r : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1) (expected : solana_pubkey.Pubkey) := NMX_R3_RegistryNativeParts.native018 ops v e t p r expected
end NMX_R3_RegistryEntry1Check
end

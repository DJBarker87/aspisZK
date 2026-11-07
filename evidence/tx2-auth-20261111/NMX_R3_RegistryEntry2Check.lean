import NMX_R3_RegistryNativeParts
import NMX_R3_RegistryScalarOps
import NMX_R3_EntryRecordGuards
import NMX_R3_EntryV2Guard
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryEntry2Check
open Aeneas Aeneas.Std AdapterRw
def check (ops : Ops) (v p : solana_pubkey.Pubkey) (t : U64) (loader : Array U8 32#usize) (r : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2) (expected : solana_pubkey.Pubkey) := NMX_R3_RegistryNativeParts.native011 ops v t loader p r expected
end NMX_R3_RegistryEntry2Check
end

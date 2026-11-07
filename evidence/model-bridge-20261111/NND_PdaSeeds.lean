import NND_Constants
import NND_RegistryOps
set_option autoImplicit false
namespace NND_PdaSeeds
open Aeneas Aeneas.Std AdapterRw NND_Carrier

def one (b : U8) : Slice U8 := Array.to_slice (Array.make 1#usize [b])

def registry1 (m : solana_pubkey.Pubkey) (b : U8) : Slice (Slice U8) :=
 Array.to_slice (Array.make 3#usize [r1_pool_adapter.VERIFIER_REGISTRY_SEED,Array.to_slice m,one b])
def registry2 (m : solana_pubkey.Pubkey) (b : U8) : Slice (Slice U8) :=
 Array.to_slice (Array.make 3#usize [r1_pool_adapter.VERIFIER_REGISTRY_V2_SEED,Array.to_slice m,one b])
def entry1 (m : solana_pubkey.Pubkey) (b : U8) : Slice (Slice U8) :=
 Array.to_slice (Array.make 5#usize [r1_pool_adapter.VERIFIER_ENTRY_SEED,Array.to_slice m,
  Array.to_slice r1_pool_adapter.PROFILE_BINDING,Array.to_slice r1_pool_adapter.RELEASE_BINDING,one b])
def entry2 (m : solana_pubkey.Pubkey) (b : U8) : Slice (Slice U8) :=
 Array.to_slice (Array.make 5#usize [r1_pool_adapter.VERIFIER_ENTRY_V2_SEED,Array.to_slice m,
  Array.to_slice r1_pool_adapter.PROFILE_BINDING,Array.to_slice r1_pool_adapter.RELEASE_BINDING,one b])
def programdata (p : solana_pubkey.Pubkey) (b : U8) : Slice (Slice U8) :=
 Array.to_slice (Array.make 2#usize [Array.to_slice p,one b])

theorem registry1_bytes (m : solana_pubkey.Pubkey) (b : U8) :
 (registry1 m b).val.map bytes = [RSL.SEED_REGISTRY,(key m).bytes,[byte b]] := by
 change [bytes r1_pool_adapter.VERIFIER_REGISTRY_SEED,(key m).bytes,[byte b]] = _
 rw [NND_Constants.registry_seed]

theorem registry2_bytes (m : solana_pubkey.Pubkey) (b : U8) :
 (registry2 m b).val.map bytes = [RSL.SEED_REGISTRY_V2,(key m).bytes,[byte b]] := by
 change [bytes r1_pool_adapter.VERIFIER_REGISTRY_V2_SEED,(key m).bytes,[byte b]] = _
 rw [NND_Constants.registry2_seed]

theorem entry1_bytes (m : solana_pubkey.Pubkey) (b : U8) :
 (entry1 m b).val.map bytes = [RSL.SEED_ENTRY,(key m).bytes,RSL.PROFILE_BINDING.bytes,RSL.RELEASE_BINDING.bytes,[byte b]] := by
 change [bytes r1_pool_adapter.VERIFIER_ENTRY_SEED,(key m).bytes,
  (key r1_pool_adapter.PROFILE_BINDING).bytes,(key r1_pool_adapter.RELEASE_BINDING).bytes,[byte b]] = _
 rw [NND_Constants.entry_seed,NND_Constants.profile,NND_Constants.release]

theorem entry2_bytes (m : solana_pubkey.Pubkey) (b : U8) :
 (entry2 m b).val.map bytes = [RSL.SEED_ENTRY_V2,(key m).bytes,RSL.PROFILE_BINDING.bytes,RSL.RELEASE_BINDING.bytes,[byte b]] := by
 change [bytes r1_pool_adapter.VERIFIER_ENTRY_V2_SEED,(key m).bytes,
  (key r1_pool_adapter.PROFILE_BINDING).bytes,(key r1_pool_adapter.RELEASE_BINDING).bytes,[byte b]] = _
 rw [NND_Constants.entry2_seed,NND_Constants.profile,NND_Constants.release]

theorem programdata_bytes (p : solana_pubkey.Pubkey) (b : U8) :
 (programdata p b).val.map bytes = [(key p).bytes,[byte b]] := rfl

#print axioms registry1_bytes
#print axioms registry2_bytes
#print axioms entry1_bytes
#print axioms entry2_bytes
#print axioms programdata_bytes
end NND_PdaSeeds

import NMX_R3_EntryRecordGuards
set_option autoImplicit false
noncomputable section
namespace NMX_R3_EntryV2Guard
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_CompareTransport
open aspis_statement.pool_v1.verifier_registry
attribute [local instance] Classical.propDecidable

def bad (v : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (e : VerifierRegistryEntryV2) (t : U64) (vpd : solana_pubkey.Pubkey) : Bool :=
 !decide (e.pool = m.key) || !decide (e.policy_binding = r1_pool_adapter.AUDIT_POLICY_BINDING)
 || !decide (e.verifier_program = v) || !decide (e.profile_binding = r1_pool_adapter.PROFILE_BINDING)
 || !decide (e.release_binding = r1_pool_adapter.RELEASE_BINDING) || e.statement_version != 1#u8
 || !decide (e.loader_program = unkey RSL.LOADER_ID) || !decide (e.programdata_address = vpd)
 || !decide (e.expected_upgrade_authority = Array.repeat 32#usize 0#u8)
 || !NIJ_ActiveSlots.active e.status e.activation_slot e.retirement_slot t

theorem value (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) (entry : VerifierRegistryEntryV2)
 (vpd : solana_pubkey.Pubkey) :
 bad v m entry t vpd = RSL.TX2_234.entryV2Bad (NMX_R3_RegistryArgs.args v p m s r e t)
  (entryV2 entry) (key vpd) := by
 unfold bad RSL.TX2_234.entryV2Bad NMX_R3_RegistryArgs.args NMX_R3_RegistryCarrier.account
 rw [NMX_R3_EntryRecordGuards.active2]
 simp only [key_ne,NND_Constants.audit,NND_Constants.profile,NND_Constants.release,
  NND_Constants.zero_key,key_forth,NMX_R3_EntryRecordGuards.byte_bne,entryV2,RSL.TERMINAL_VERSION]
 rfl

#print axioms value
end NMX_R3_EntryV2Guard
end

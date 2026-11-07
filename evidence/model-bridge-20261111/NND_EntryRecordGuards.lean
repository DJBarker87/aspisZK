import NND_RegistryRecordGuards
set_option autoImplicit false
noncomputable section
namespace NND_EntryRecordGuards
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_CompareTransport
open aspis_statement.pool_v1.verifier_registry
attribute [local instance] Classical.propDecidable

theorem active1 (e : VerifierRegistryEntryV1) (t : U64) :
 NIJ_ActiveSlots.active e.status e.activation_slot e.retirement_slot t = (entryV1 e).is_active_at (slot t) := by
 have h := NND_RegistryPredicates.active1 e t
 change Result.ok _ = Result.ok _ at h
 exact Result.ok.inj h

theorem active2 (e : VerifierRegistryEntryV2) (t : U64) :
 NIJ_ActiveSlots.active e.status e.activation_slot e.retirement_slot t = (entryV2 e).is_active_at (slot t) := by
 have h := NND_RegistryPredicates.active2 e t
 change Result.ok _ = Result.ok _ at h
 exact Result.ok.inj h

theorem byte_bne (x y : U8) : (x != y) = (byte x != byte y) := by
 simp only [bne,byte_beq]

def bad1 (v : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (e : VerifierRegistryEntryV1) (t : U64) : Bool :=
 !decide (e.pool = m.key) || !decide (e.policy_binding = r1_pool_adapter.AUDIT_POLICY_BINDING)
 || !decide (e.verifier_program = v) || !decide (e.profile_binding = r1_pool_adapter.PROFILE_BINDING)
 || !decide (e.release_binding = r1_pool_adapter.RELEASE_BINDING) || e.statement_version != 1#u8
 || !NIJ_ActiveSlots.active e.status e.activation_slot e.retirement_slot t

theorem entry1 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) (entry : VerifierRegistryEntryV1) :
 bad1 v m entry t = RSL.TX2_234.entryV1Bad (NND_RegistryArgs.args v p m s r e t) (entryV1 entry) := by
 unfold bad1 RSL.TX2_234.entryV1Bad NND_RegistryArgs.args account
 rw [active1]
 simp only [key_ne,NND_Constants.audit,NND_Constants.profile,NND_Constants.release,byte_bne,
  entryV1,RSL.TERMINAL_VERSION]
 rfl

#print axioms active1
#print axioms active2
#print axioms byte_bne
#print axioms entry1
end NND_EntryRecordGuards
end

import NMX_R3_RegistryPartErasure
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistrySource
open Aeneas Aeneas.Std AdapterRw NMX_R3_RegistryProgram
theorem factor (ops : Ops)
  (verifier_program : solana_pubkey.Pubkey)
  (pool_program : solana_pubkey.Pubkey)
  (master_account : r1_pool_adapter.owned.OwnedAccount)
  (master :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
  (registry_account : r1_pool_adapter.owned.OwnedAccount)
  (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : Std.U64)
 :
 NMX_R3_RegistryNativeParts.native000 ops verifier_program pool_program master_account master registry_account entry_account current_slot =
 NMX_R3_RegistryEmitted.body ops verifier_program pool_program master_account master registry_account entry_account current_slot := by
 simp only [NMX_R3_RegistryNativeParts.native000, NMX_R3_RegistryNativeParts.native001, NMX_R3_RegistryNativeParts.native002, NMX_R3_RegistryNativeParts.native003, NMX_R3_RegistryNativeParts.native004, NMX_R3_RegistryNativeParts.native005, NMX_R3_RegistryNativeParts.native006, NMX_R3_RegistryNativeParts.native007, NMX_R3_RegistryNativeParts.native008, NMX_R3_RegistryNativeParts.native009, NMX_R3_RegistryNativeParts.native010, NMX_R3_RegistryNativeParts.native011, NMX_R3_RegistryNativeParts.native012, NMX_R3_RegistryNativeParts.native013, NMX_R3_RegistryNativeParts.native014, NMX_R3_RegistryNativeParts.native015, NMX_R3_RegistryNativeParts.native016, NMX_R3_RegistryNativeParts.native017, NMX_R3_RegistryNativeParts.native018, NMX_R3_RegistryEmitted.body]
 <;> (repeat' first | rfl | (apply NMX_R3_RegistryErasureCut2.bind_congr; intro x) | split)
 <;> first | rfl | (rename_i h; cases h <;> rfl)

#print axioms factor
theorem erase_root (ops : Ops)
  (verifier_program : solana_pubkey.Pubkey)
  (pool_program : solana_pubkey.Pubkey)
  (master_account : r1_pool_adapter.owned.OwnedAccount)
  (master :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
  (registry_account : r1_pool_adapter.owned.OwnedAccount)
  (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : Std.U64)
 :
 erase ops (NMX_R3_RegistryScriptParts.script000 ops verifier_program pool_program master_account master registry_account entry_account current_slot) =
 NMX_R3_RegistryNativeParts.native000 ops verifier_program pool_program master_account master registry_account entry_account current_slot := by
 simp only [NMX_R3_RegistryScriptParts.script000, scalar, data, pda, erase_bind, erase_call, commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native000, NMX_R3_RegistryPartErasure.step001]
 <;> (repeat' first | rfl | (apply NMX_R3_RegistryErasureCut2.bind_congr; intro x) | split)
 <;> first | rfl | (rename_i h; cases h <;> rfl)
#print axioms erase_root
end NMX_R3_RegistrySource
end

import NMX_R3_RegistryErasureTail
import NMX_R3_RegistryErasureCut2
import NMX_R3_RegistryScriptParts
import NMX_R3_RegistryNativeParts
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryPartErasure
open Aeneas Aeneas.Std Result AdapterRw NMX_R3_RegistryProgram

open NMX_R3_RegistryErasureCut2

open NMX_R3_RegistryErasureTail

theorem step008 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (a6 : Array U8 32#usize) (loader : Array U8 32#usize) (p : Array U8 32#usize) (registry_program : Array U8 32#usize) (val4 : Slice U8) :
 erase ops (NMX_R3_RegistryScriptParts.script008 ops verifier_program entry_account current_slot a6 loader p registry_program val4) =
 NMX_R3_RegistryNativeParts.native008 ops verifier_program entry_account current_slot a6 loader p registry_program val4 := by
 simp only [NMX_R3_RegistryScriptParts.script008, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native008, NMX_R3_RegistryProgram.control.match_1,
  step018, step017, step016, step015, step014, step013, step012, step011, step010, step009] <;> (repeat' first | rfl | (apply NMX_R3_RegistryErasureCut2.bind_congr; intro x) | split) <;> first | rfl | (rename_i h; cases h <;> rfl)
#print axioms step008

theorem step007 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (a6 : Array U8 32#usize) (loader : Array U8 32#usize) (p : Array U8 32#usize) (registry_program : Array U8 32#usize) :
 erase ops (NMX_R3_RegistryScriptParts.script007 ops verifier_program entry_account current_slot a6 loader p registry_program) =
 NMX_R3_RegistryNativeParts.native007 ops verifier_program entry_account current_slot a6 loader p registry_program := by
 simp only [NMX_R3_RegistryScriptParts.script007, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native007, NMX_R3_RegistryProgram.control.match_1,
  step018, step017, step016, step015, step014, step013, step012, step011, step010, step009, step008] <;> (repeat' first | rfl | (apply NMX_R3_RegistryErasureCut2.bind_congr; intro x) | split) <;> first | rfl | (rename_i h; cases h <;> rfl)
#print axioms step007

theorem step006 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (loader : Array U8 32#usize) (p : Array U8 32#usize) (registry_program : Array U8 32#usize) (val1 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2) (val3 : solana_pubkey.Pubkey) :
 erase ops (NMX_R3_RegistryScriptParts.script006 ops verifier_program master entry_account current_slot loader p registry_program val1 val3) =
 NMX_R3_RegistryNativeParts.native006 ops verifier_program master entry_account current_slot loader p registry_program val1 val3 := by
 simp only [NMX_R3_RegistryScriptParts.script006, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native006, NMX_R3_RegistryProgram.control.match_1,
  step018, step017, step016, step015, step014, step013, step012, step011, step010, step009, step008, step007] <;> (repeat' first | rfl | (apply NMX_R3_RegistryErasureCut2.bind_congr; intro x) | split) <;> first | rfl | (rename_i h; cases h <;> rfl)
#print axioms step006

theorem step005 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) (registry_account : r1_pool_adapter.owned.OwnedAccount) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (loader : Array U8 32#usize) (p : Array U8 32#usize) (registry_program : Array U8 32#usize) (val1 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2) (val2 : solana_pubkey.Pubkey) :
 erase ops (NMX_R3_RegistryScriptParts.script005 ops verifier_program master registry_account entry_account current_slot loader p registry_program val1 val2) =
 NMX_R3_RegistryNativeParts.native005 ops verifier_program master registry_account entry_account current_slot loader p registry_program val1 val2 := by
 simp only [NMX_R3_RegistryScriptParts.script005, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native005, NMX_R3_RegistryProgram.control.match_1,
  step018, step017, step016, step015, step014, step013, step012, step011, step010, step009, step008, step007, step006] <;> (repeat' first | rfl | (apply NMX_R3_RegistryErasureCut2.bind_congr; intro x) | split) <;> first | rfl | (rename_i h; cases h <;> rfl)
#print axioms step005

theorem step004 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (master_account : r1_pool_adapter.owned.OwnedAccount) (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) (registry_account : r1_pool_adapter.owned.OwnedAccount) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (loader : Array U8 32#usize) (registry_program : Array U8 32#usize) (val1 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2) :
 erase ops (NMX_R3_RegistryScriptParts.script004 ops verifier_program master_account master registry_account entry_account current_slot loader registry_program val1) =
 NMX_R3_RegistryNativeParts.native004 ops verifier_program master_account master registry_account entry_account current_slot loader registry_program val1 := by
 simp only [NMX_R3_RegistryScriptParts.script004, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native004, NMX_R3_RegistryProgram.control.match_1,
  step018, step017, step016, step015, step014, step013, step012, step011, step010, step009, step008, step007, step006, step005] <;> (repeat' first | rfl | (apply NMX_R3_RegistryErasureCut2.bind_congr; intro x) | split) <;> first | rfl | (rename_i h; cases h <;> rfl)
#print axioms step004

theorem step003 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (master_account : r1_pool_adapter.owned.OwnedAccount) (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) (registry_account : r1_pool_adapter.owned.OwnedAccount) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (loader : Array U8 32#usize) (registry_program : Array U8 32#usize) (val : Slice U8) :
 erase ops (NMX_R3_RegistryScriptParts.script003 ops verifier_program master_account master registry_account entry_account current_slot loader registry_program val) =
 NMX_R3_RegistryNativeParts.native003 ops verifier_program master_account master registry_account entry_account current_slot loader registry_program val := by
 simp only [NMX_R3_RegistryScriptParts.script003, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native003, NMX_R3_RegistryProgram.control.match_1,
  step018, step017, step016, step015, step014, step013, step012, step011, step010, step009, step008, step007, step006, step005, step004] <;> (repeat' first | rfl | (apply NMX_R3_RegistryErasureCut2.bind_congr; intro x) | split) <;> first | rfl | (rename_i h; cases h <;> rfl)
#print axioms step003

theorem step002 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (master_account : r1_pool_adapter.owned.OwnedAccount) (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) (registry_account : r1_pool_adapter.owned.OwnedAccount) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (registry_program : Array U8 32#usize) :
 erase ops (NMX_R3_RegistryScriptParts.script002 ops verifier_program master_account master registry_account entry_account current_slot registry_program) =
 NMX_R3_RegistryNativeParts.native002 ops verifier_program master_account master registry_account entry_account current_slot registry_program := by
 simp only [NMX_R3_RegistryScriptParts.script002, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native002, NMX_R3_RegistryProgram.control.match_1,
  step018, step017, step016, step015, step014, step013, step012, step011, step010, step009, step008, step007, step006, step005, step004, step003] <;> (repeat' first | rfl | (apply NMX_R3_RegistryErasureCut2.bind_congr; intro x) | split) <;> first | rfl | (rename_i h; cases h <;> rfl)
#print axioms step002

theorem step001 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (master_account : r1_pool_adapter.owned.OwnedAccount) (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) (registry_account : r1_pool_adapter.owned.OwnedAccount) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (a2 : Array U8 32#usize) :
 erase ops (NMX_R3_RegistryScriptParts.script001 ops verifier_program master_account master registry_account entry_account current_slot a2) =
 NMX_R3_RegistryNativeParts.native001 ops verifier_program master_account master registry_account entry_account current_slot a2 := by
 simp only [NMX_R3_RegistryScriptParts.script001, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native001, NMX_R3_RegistryProgram.control.match_1,
  step018, step017, step016, step015, step014, step013, step012, step011, step010, step009, step008, step007, step006, step005, step004, step003, step002] <;> (repeat' first | rfl | (apply NMX_R3_RegistryErasureCut2.bind_congr; intro x) | split) <;> first | rfl | (rename_i h; cases h <;> rfl)
#print axioms step001

end NMX_R3_RegistryPartErasure
end

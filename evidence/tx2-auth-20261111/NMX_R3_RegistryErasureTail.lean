import NMX_R3_RegistryErasureCut2
import NMX_R3_RegistryScriptParts
import NMX_R3_RegistryNativeParts
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryErasureTail
open Aeneas Aeneas.Std Result AdapterRw NMX_R3_RegistryProgram

open NMX_R3_RegistryErasureCut2

theorem step016 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (p : Array U8 32#usize) (registry_program : Array U8 32#usize) (val3 : Slice U8) :
 erase ops (NMX_R3_RegistryScriptParts.script016 ops verifier_program entry_account current_slot p registry_program val3) =
 NMX_R3_RegistryNativeParts.native016 ops verifier_program entry_account current_slot p registry_program val3 := by
 simp only [NMX_R3_RegistryScriptParts.script016, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native016, NMX_R3_RegistryProgram.control.match_1,
  step018, step017] <;> (repeat' first | rfl | (apply NMX_R3_RegistryErasureCut2.bind_congr; intro x) | split) <;> first | rfl | (rename_i h; cases h <;> rfl)
#print axioms step016

theorem step015 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (p : Array U8 32#usize) (registry_program : Array U8 32#usize) :
 erase ops (NMX_R3_RegistryScriptParts.script015 ops verifier_program entry_account current_slot p registry_program) =
 NMX_R3_RegistryNativeParts.native015 ops verifier_program entry_account current_slot p registry_program := by
 simp only [NMX_R3_RegistryScriptParts.script015, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native015, NMX_R3_RegistryProgram.control.match_1,
  step018, step017, step016] <;> (repeat' first | rfl | (apply NMX_R3_RegistryErasureCut2.bind_congr; intro x) | split) <;> first | rfl | (rename_i h; cases h <;> rfl)
#print axioms step015

theorem step014 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) (registry_account : r1_pool_adapter.owned.OwnedAccount) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (p : Array U8 32#usize) (registry_program : Array U8 32#usize) (val1 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1) (val2 : solana_pubkey.Pubkey) :
 erase ops (NMX_R3_RegistryScriptParts.script014 ops verifier_program master registry_account entry_account current_slot p registry_program val1 val2) =
 NMX_R3_RegistryNativeParts.native014 ops verifier_program master registry_account entry_account current_slot p registry_program val1 val2 := by
 simp only [NMX_R3_RegistryScriptParts.script014, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native014, NMX_R3_RegistryProgram.control.match_1,
  step018, step017, step016, step015] <;> (repeat' first | rfl | (apply NMX_R3_RegistryErasureCut2.bind_congr; intro x) | split) <;> first | rfl | (rename_i h; cases h <;> rfl)
#print axioms step014

theorem step013 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (master_account : r1_pool_adapter.owned.OwnedAccount) (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) (registry_account : r1_pool_adapter.owned.OwnedAccount) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (registry_program : Array U8 32#usize) (val1 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1) :
 erase ops (NMX_R3_RegistryScriptParts.script013 ops verifier_program master_account master registry_account entry_account current_slot registry_program val1) =
 NMX_R3_RegistryNativeParts.native013 ops verifier_program master_account master registry_account entry_account current_slot registry_program val1 := by
 simp only [NMX_R3_RegistryScriptParts.script013, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native013, NMX_R3_RegistryProgram.control.match_1,
  step018, step017, step016, step015, step014] <;> (repeat' first | rfl | (apply NMX_R3_RegistryErasureCut2.bind_congr; intro x) | split) <;> first | rfl | (rename_i h; cases h <;> rfl)
#print axioms step013

theorem step012 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (master_account : r1_pool_adapter.owned.OwnedAccount) (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) (registry_account : r1_pool_adapter.owned.OwnedAccount) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (registry_program : Array U8 32#usize) (val : Slice U8) :
 erase ops (NMX_R3_RegistryScriptParts.script012 ops verifier_program master_account master registry_account entry_account current_slot registry_program val) =
 NMX_R3_RegistryNativeParts.native012 ops verifier_program master_account master registry_account entry_account current_slot registry_program val := by
 simp only [NMX_R3_RegistryScriptParts.script012, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native012, NMX_R3_RegistryProgram.control.match_1,
  step018, step017, step016, step015, step014, step013] <;> (repeat' first | rfl | (apply NMX_R3_RegistryErasureCut2.bind_congr; intro x) | split) <;> first | rfl | (rename_i h; cases h <;> rfl)
#print axioms step012

theorem step011 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (current_slot : U64) (a6 : Array U8 32#usize) (p : Array U8 32#usize) (val5 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2) (val7 : solana_pubkey.Pubkey) :
 erase ops (NMX_R3_RegistryScriptParts.script011 ops verifier_program current_slot a6 p val5 val7) =
 NMX_R3_RegistryNativeParts.native011 ops verifier_program current_slot a6 p val5 val7 := by
 simp only [NMX_R3_RegistryScriptParts.script011, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native011,
  step018, step017, step016, step015, step014, step013, step012] <;> (repeat' first | rfl | (apply NMX_R3_RegistryErasureCut2.bind_congr; intro x) | split) <;> first | rfl | (rename_i h; cases h <;> rfl)
#print axioms step011

theorem step010 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (a6 : Array U8 32#usize) (loader : Array U8 32#usize) (p : Array U8 32#usize) (val5 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2) (val6 : solana_pubkey.Pubkey) :
 erase ops (NMX_R3_RegistryScriptParts.script010 ops verifier_program entry_account current_slot a6 loader p val5 val6) =
 NMX_R3_RegistryNativeParts.native010 ops verifier_program entry_account current_slot a6 loader p val5 val6 := by
 simp only [NMX_R3_RegistryScriptParts.script010, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native010, NMX_R3_RegistryProgram.control.match_1,
  step018, step017, step016, step015, step014, step013, step012, step011] <;> (repeat' first | rfl | (apply NMX_R3_RegistryErasureCut2.bind_congr; intro x) | split) <;> first | rfl | (rename_i h; cases h <;> rfl)
#print axioms step010

theorem step009 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (a6 : Array U8 32#usize) (loader : Array U8 32#usize) (p : Array U8 32#usize) (registry_program : Array U8 32#usize) (val5 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2) :
 erase ops (NMX_R3_RegistryScriptParts.script009 ops verifier_program entry_account current_slot a6 loader p registry_program val5) =
 NMX_R3_RegistryNativeParts.native009 ops verifier_program entry_account current_slot a6 loader p registry_program val5 := by
 simp only [NMX_R3_RegistryScriptParts.script009, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native009, NMX_R3_RegistryProgram.control.match_1,
  step018, step017, step016, step015, step014, step013, step012, step011, step010] <;> (repeat' first | rfl | (apply NMX_R3_RegistryErasureCut2.bind_congr; intro x) | split) <;> first | rfl | (rename_i h; cases h <;> rfl)
#print axioms step009

end NMX_R3_RegistryErasureTail
end

import NMX_R3_RegistryScriptParts
import NMX_R3_RegistryNativeParts
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryPartErasure
open Aeneas Aeneas.Std Result AdapterRw NMX_R3_RegistryProgram

theorem step018 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (p : Array U8 32#usize) (val4 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1) (val5 : solana_pubkey.Pubkey) :
 erase ops (NMX_R3_RegistryScriptParts.script018 ops verifier_program entry_account current_slot p val4 val5) =
 NMX_R3_RegistryNativeParts.native018 ops verifier_program entry_account current_slot p val4 val5 := by
 simp only [NMX_R3_RegistryScriptParts.script018, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native018
  ]
#print axioms step018

theorem step017 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (p : Array U8 32#usize) (registry_program : Array U8 32#usize) (val4 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1) :
 erase ops (NMX_R3_RegistryScriptParts.script017 ops verifier_program entry_account current_slot p registry_program val4) =
 NMX_R3_RegistryNativeParts.native017 ops verifier_program entry_account current_slot p registry_program val4 := by
 simp only [NMX_R3_RegistryScriptParts.script017, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native017,
  step018]
#print axioms step017

theorem step016 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (p : Array U8 32#usize) (registry_program : Array U8 32#usize) (val3 : Slice U8) :
 erase ops (NMX_R3_RegistryScriptParts.script016 ops verifier_program entry_account current_slot p registry_program val3) =
 NMX_R3_RegistryNativeParts.native016 ops verifier_program entry_account current_slot p registry_program val3 := by
 simp only [NMX_R3_RegistryScriptParts.script016, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native016,
  step018, step017]
#print axioms step016

theorem step015 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (p : Array U8 32#usize) (registry_program : Array U8 32#usize) :
 erase ops (NMX_R3_RegistryScriptParts.script015 ops verifier_program entry_account current_slot p registry_program) =
 NMX_R3_RegistryNativeParts.native015 ops verifier_program entry_account current_slot p registry_program := by
 simp only [NMX_R3_RegistryScriptParts.script015, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native015,
  step018, step017, step016]
#print axioms step015

theorem step014 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) (registry_account : r1_pool_adapter.owned.OwnedAccount) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (p : Array U8 32#usize) (registry_program : Array U8 32#usize) (val1 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1) (val2 : solana_pubkey.Pubkey) :
 erase ops (NMX_R3_RegistryScriptParts.script014 ops verifier_program master registry_account entry_account current_slot p registry_program val1 val2) =
 NMX_R3_RegistryNativeParts.native014 ops verifier_program master registry_account entry_account current_slot p registry_program val1 val2 := by
 simp only [NMX_R3_RegistryScriptParts.script014, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native014,
  step018, step017, step016, step015]
#print axioms step014

theorem step013 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (master_account : r1_pool_adapter.owned.OwnedAccount) (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) (registry_account : r1_pool_adapter.owned.OwnedAccount) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (registry_program : Array U8 32#usize) (val1 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1) :
 erase ops (NMX_R3_RegistryScriptParts.script013 ops verifier_program master_account master registry_account entry_account current_slot registry_program val1) =
 NMX_R3_RegistryNativeParts.native013 ops verifier_program master_account master registry_account entry_account current_slot registry_program val1 := by
 simp only [NMX_R3_RegistryScriptParts.script013, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native013,
  step018, step017, step016, step015, step014]
#print axioms step013

theorem step012 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (master_account : r1_pool_adapter.owned.OwnedAccount) (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) (registry_account : r1_pool_adapter.owned.OwnedAccount) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (registry_program : Array U8 32#usize) (val : Slice U8) :
 erase ops (NMX_R3_RegistryScriptParts.script012 ops verifier_program master_account master registry_account entry_account current_slot registry_program val) =
 NMX_R3_RegistryNativeParts.native012 ops verifier_program master_account master registry_account entry_account current_slot registry_program val := by
 simp only [NMX_R3_RegistryScriptParts.script012, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native012,
  step018, step017, step016, step015, step014, step013]
#print axioms step012

theorem step011 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (current_slot : U64) (a6 : Array U8 32#usize) (p : Array U8 32#usize) (val5 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2) (val7 : solana_pubkey.Pubkey) :
 erase ops (NMX_R3_RegistryScriptParts.script011 ops verifier_program current_slot a6 p val5 val7) =
 NMX_R3_RegistryNativeParts.native011 ops verifier_program current_slot a6 p val5 val7 := by
 simp only [NMX_R3_RegistryScriptParts.script011, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native011,
  step018, step017, step016, step015, step014, step013, step012]
#print axioms step011

theorem step010 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (a6 : Array U8 32#usize) (loader : Array U8 32#usize) (p : Array U8 32#usize) (val5 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2) (val6 : solana_pubkey.Pubkey) :
 erase ops (NMX_R3_RegistryScriptParts.script010 ops verifier_program entry_account current_slot a6 loader p val5 val6) =
 NMX_R3_RegistryNativeParts.native010 ops verifier_program entry_account current_slot a6 loader p val5 val6 := by
 simp only [NMX_R3_RegistryScriptParts.script010, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native010,
  step018, step017, step016, step015, step014, step013, step012, step011]
#print axioms step010

theorem step009 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (a6 : Array U8 32#usize) (loader : Array U8 32#usize) (p : Array U8 32#usize) (registry_program : Array U8 32#usize) (val5 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2) :
 erase ops (NMX_R3_RegistryScriptParts.script009 ops verifier_program entry_account current_slot a6 loader p registry_program val5) =
 NMX_R3_RegistryNativeParts.native009 ops verifier_program entry_account current_slot a6 loader p registry_program val5 := by
 simp only [NMX_R3_RegistryScriptParts.script009, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native009,
  step018, step017, step016, step015, step014, step013, step012, step011, step010]
#print axioms step009

theorem step008 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (a6 : Array U8 32#usize) (loader : Array U8 32#usize) (p : Array U8 32#usize) (registry_program : Array U8 32#usize) (val4 : Slice U8) :
 erase ops (NMX_R3_RegistryScriptParts.script008 ops verifier_program entry_account current_slot a6 loader p registry_program val4) =
 NMX_R3_RegistryNativeParts.native008 ops verifier_program entry_account current_slot a6 loader p registry_program val4 := by
 simp only [NMX_R3_RegistryScriptParts.script008, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native008,
  step018, step017, step016, step015, step014, step013, step012, step011, step010, step009]
#print axioms step008

theorem step007 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (a6 : Array U8 32#usize) (loader : Array U8 32#usize) (p : Array U8 32#usize) (registry_program : Array U8 32#usize) :
 erase ops (NMX_R3_RegistryScriptParts.script007 ops verifier_program entry_account current_slot a6 loader p registry_program) =
 NMX_R3_RegistryNativeParts.native007 ops verifier_program entry_account current_slot a6 loader p registry_program := by
 simp only [NMX_R3_RegistryScriptParts.script007, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native007,
  step018, step017, step016, step015, step014, step013, step012, step011, step010, step009, step008]
#print axioms step007

theorem step006 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (loader : Array U8 32#usize) (p : Array U8 32#usize) (registry_program : Array U8 32#usize) (val1 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2) (val3 : solana_pubkey.Pubkey) :
 erase ops (NMX_R3_RegistryScriptParts.script006 ops verifier_program master entry_account current_slot loader p registry_program val1 val3) =
 NMX_R3_RegistryNativeParts.native006 ops verifier_program master entry_account current_slot loader p registry_program val1 val3 := by
 simp only [NMX_R3_RegistryScriptParts.script006, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native006,
  step018, step017, step016, step015, step014, step013, step012, step011, step010, step009, step008, step007]
#print axioms step006

theorem step005 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) (registry_account : r1_pool_adapter.owned.OwnedAccount) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (loader : Array U8 32#usize) (p : Array U8 32#usize) (registry_program : Array U8 32#usize) (val1 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2) (val2 : solana_pubkey.Pubkey) :
 erase ops (NMX_R3_RegistryScriptParts.script005 ops verifier_program master registry_account entry_account current_slot loader p registry_program val1 val2) =
 NMX_R3_RegistryNativeParts.native005 ops verifier_program master registry_account entry_account current_slot loader p registry_program val1 val2 := by
 simp only [NMX_R3_RegistryScriptParts.script005, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native005,
  step018, step017, step016, step015, step014, step013, step012, step011, step010, step009, step008, step007, step006]
#print axioms step005

theorem step004 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (master_account : r1_pool_adapter.owned.OwnedAccount) (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) (registry_account : r1_pool_adapter.owned.OwnedAccount) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (loader : Array U8 32#usize) (registry_program : Array U8 32#usize) (val1 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2) :
 erase ops (NMX_R3_RegistryScriptParts.script004 ops verifier_program master_account master registry_account entry_account current_slot loader registry_program val1) =
 NMX_R3_RegistryNativeParts.native004 ops verifier_program master_account master registry_account entry_account current_slot loader registry_program val1 := by
 simp only [NMX_R3_RegistryScriptParts.script004, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native004,
  step018, step017, step016, step015, step014, step013, step012, step011, step010, step009, step008, step007, step006, step005]
#print axioms step004

theorem step003 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (master_account : r1_pool_adapter.owned.OwnedAccount) (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) (registry_account : r1_pool_adapter.owned.OwnedAccount) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (loader : Array U8 32#usize) (registry_program : Array U8 32#usize) (val : Slice U8) :
 erase ops (NMX_R3_RegistryScriptParts.script003 ops verifier_program master_account master registry_account entry_account current_slot loader registry_program val) =
 NMX_R3_RegistryNativeParts.native003 ops verifier_program master_account master registry_account entry_account current_slot loader registry_program val := by
 simp only [NMX_R3_RegistryScriptParts.script003, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native003,
  step018, step017, step016, step015, step014, step013, step012, step011, step010, step009, step008, step007, step006, step005, step004]
#print axioms step003

theorem step002 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (master_account : r1_pool_adapter.owned.OwnedAccount) (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) (registry_account : r1_pool_adapter.owned.OwnedAccount) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (registry_program : Array U8 32#usize) :
 erase ops (NMX_R3_RegistryScriptParts.script002 ops verifier_program master_account master registry_account entry_account current_slot registry_program) =
 NMX_R3_RegistryNativeParts.native002 ops verifier_program master_account master registry_account entry_account current_slot registry_program := by
 simp only [NMX_R3_RegistryScriptParts.script002, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native002,
  step018, step017, step016, step015, step014, step013, step012, step011, step010, step009, step008, step007, step006, step005, step004, step003]
#print axioms step002

theorem step001 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (master_account : r1_pool_adapter.owned.OwnedAccount) (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) (registry_account : r1_pool_adapter.owned.OwnedAccount) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (a2 : Array U8 32#usize) :
 erase ops (NMX_R3_RegistryScriptParts.script001 ops verifier_program master_account master registry_account entry_account current_slot a2) =
 NMX_R3_RegistryNativeParts.native001 ops verifier_program master_account master registry_account entry_account current_slot a2 := by
 simp only [NMX_R3_RegistryScriptParts.script001, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native001,
  step018, step017, step016, step015, step014, step013, step012, step011, step010, step009, step008, step007, step006, step005, step004, step003, step002]
#print axioms step001

end NMX_R3_RegistryPartErasure
end

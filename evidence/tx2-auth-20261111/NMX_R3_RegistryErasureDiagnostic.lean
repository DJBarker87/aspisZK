import NMX_R3_RegistryScriptParts
import NMX_R3_RegistryNativeParts
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryErasureDiagnostic
open Aeneas Aeneas.Std Result AdapterRw NMX_R3_RegistryProgram

theorem step018 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (p : Array U8 32#usize) (val4 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1) (val5 : solana_pubkey.Pubkey) :
 erase ops (NMX_R3_RegistryScriptParts.script018 ops verifier_program entry_account current_slot p val4 val5) =
 NMX_R3_RegistryNativeParts.native018 ops verifier_program entry_account current_slot p val4 val5 := by
 simp only [NMX_R3_RegistryScriptParts.script018, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native018
  ]
 set_option pp.all true in trace_state
 done
#print axioms step018

theorem step017 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (p : Array U8 32#usize) (registry_program : Array U8 32#usize) (val4 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1) :
 erase ops (NMX_R3_RegistryScriptParts.script017 ops verifier_program entry_account current_slot p registry_program val4) =
 NMX_R3_RegistryNativeParts.native017 ops verifier_program entry_account current_slot p registry_program val4 := by
 simp only [NMX_R3_RegistryScriptParts.script017, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native017,
  step018]
 set_option pp.all true in trace_state
 done
#print axioms step017

end NMX_R3_RegistryErasureDiagnostic
end

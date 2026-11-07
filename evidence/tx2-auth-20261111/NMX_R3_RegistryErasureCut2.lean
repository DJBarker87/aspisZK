import NMX_R3_RegistryScriptParts
import NMX_R3_RegistryNativeParts
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryErasureCut2
open Aeneas Aeneas.Std Result AdapterRw NMX_R3_RegistryProgram

theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
 (h : ∀ a, f a = g a) : (r >>= f) = (r >>= g) :=
 congrArg (fun k => r >>= k) (funext h)
#print axioms bind_congr

theorem step018 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (p : Array U8 32#usize) (val4 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1) (val5 : solana_pubkey.Pubkey) :
 erase ops (NMX_R3_RegistryScriptParts.script018 ops verifier_program entry_account current_slot p val4 val5) =
 NMX_R3_RegistryNativeParts.native018 ops verifier_program entry_account current_slot p val4 val5 := by
 simp only [NMX_R3_RegistryScriptParts.script018, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native018
  ] <;> (repeat' first | (apply bind_congr; intro x) | split) <;> first | rfl | (rename_i h; cases h <;> rfl)
#print axioms step018

theorem step017 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (p : Array U8 32#usize) (registry_program : Array U8 32#usize) (val4 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1) :
 erase ops (NMX_R3_RegistryScriptParts.script017 ops verifier_program entry_account current_slot p registry_program val4) =
 NMX_R3_RegistryNativeParts.native017 ops verifier_program entry_account current_slot p registry_program val4 := by
 simp only [NMX_R3_RegistryScriptParts.script017, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_if, erase_control, erase_pure, NMX_R3_RegistryNativeParts.native017, NMX_R3_RegistryNativeParts.native017.match_1, NMX_R3_RegistryProgram.control.match_1,
  step018] <;> (repeat' first | (apply bind_congr; intro x) | split) <;> first | rfl | (rename_i h; cases h <;> rfl)
#print axioms step017

end NMX_R3_RegistryErasureCut2
end

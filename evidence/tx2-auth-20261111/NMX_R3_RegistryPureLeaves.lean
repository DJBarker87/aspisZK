import NMX_R3_RegistryPure
import NMX_R3_RegistryScriptParts
import NMX_R3_RegistryNativeParts
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryPureLeaves
open Aeneas Aeneas.Std AdapterRw NMX_R3_RegistryProgram NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws
theorem step018 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (p : Array U8 32#usize) (val4 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1) (val5 : solana_pubkey.Pubkey) :
 eval (NMX_R3_RegistryScriptParts.script018 ops verifier_program entry_account current_slot p val4 val5) =
 scalarSpec (NMX_R3_RegistryNativeParts.native018 ops verifier_program entry_account current_slot p val4 val5) := by
 simp only [NMX_R3_RegistryScriptParts.script018,NMX_R3_RegistryNativeParts.native018,
  NMX_R3_RegistryEffects.eval_bind,eval_scalar,eval_if,eval_pure,
  NMX_R3_RegistryPure.bind,NMX_R3_RegistryPure.ite,NMX_R3_RegistryPure.ok]
#print axioms step018

end NMX_R3_RegistryPureLeaves
end

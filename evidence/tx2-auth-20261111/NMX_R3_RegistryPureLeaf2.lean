import NMX_R3_RegistryPureLeaves
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryPureLeaf2
open Aeneas Aeneas.Std AdapterRw NMX_R3_RegistryProgram NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws
theorem step011 (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (current_slot : U64) (a6 : Array U8 32#usize) (p : Array U8 32#usize) (val5 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2) (val7 : solana_pubkey.Pubkey) :
 eval (NMX_R3_RegistryScriptParts.script011 ops verifier_program current_slot a6 p val5 val7) =
 scalarSpec (NMX_R3_RegistryNativeParts.native011 ops verifier_program current_slot a6 p val5 val7) := by
 simp only [NMX_R3_RegistryScriptParts.script011,NMX_R3_RegistryNativeParts.native011,
  NMX_R3_RegistryEffects.eval_bind,eval_scalar,eval_if,eval_pure,
  NMX_R3_RegistryPure.bind,NMX_R3_RegistryPure.ite,NMX_R3_RegistryPure.ok]
#print axioms step011
end NMX_R3_RegistryPureLeaf2
end

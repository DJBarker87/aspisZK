import NMX_R3_RegistryScript
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryScriptErasure
open Aeneas Aeneas.Std Result AdapterRw NMX_R3_RegistryProgram
theorem source (ops : Ops) (v p : solana_pubkey.Pubkey)
 (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 erase ops (NMX_R3_RegistryScript.script ops v p m s r e t) =
 NMX_R3_RegistryEmitted.body ops v p m s r e t := by
 simp only [NMX_R3_RegistryScript.script, scalar, data, pda, erase_bind, erase_call,
  commandValue, erase_pure, erase_if, erase_control, NMX_R3_RegistryEmitted.body, erase]
#print axioms source
end NMX_R3_RegistryScriptErasure
end

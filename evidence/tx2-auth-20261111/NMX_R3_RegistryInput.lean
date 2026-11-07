import NMX_R3_RegistryProjection
import NMX_R3_RegistryArgs
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryInput
open Aeneas Aeneas.Std AdapterRw NND_Carrier

structure Input where
 verifier : solana_pubkey.Pubkey
 pool : solana_pubkey.Pubkey
 masterAccount : r1_pool_adapter.owned.OwnedAccount
 master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1
 registry : r1_pool_adapter.owned.OwnedAccount
 entry : r1_pool_adapter.owned.OwnedAccount
 slot : U64

def reify (a : RSL.TX2_234.Args) : Input :=
 ⟨unkey a.verifier_program,unkey a.pool_program,
  NMX_R3_RegistryProjection.nativeAccount a.master_account,
  NMX_R3_RegistryProjection.nativeMaster a.master.verifier_policy,
  NMX_R3_RegistryProjection.nativeAccount a.registry_account,
  NMX_R3_RegistryProjection.nativeAccount a.entry_account,unslot a.current_slot⟩

def image (a : Input) : RSL.TX2_234.Args :=
 NMX_R3_RegistryArgs.args a.verifier a.pool a.masterAccount a.master a.registry a.entry a.slot

theorem roundtrip (a : RSL.TX2_234.Args) : image (reify a) = NMX_R3_RegistryProjection.args a := by
 cases a
 simp only [image,reify,NMX_R3_RegistryArgs.args,NMX_R3_RegistryProjection.args,
  NMX_R3_RegistryProjection.account_image,key_forth,NND_Carrier.slot_forth]
#print axioms roundtrip
end NMX_R3_RegistryInput
end

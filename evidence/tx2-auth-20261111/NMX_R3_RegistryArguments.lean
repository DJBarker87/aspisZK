import NMX_R3_RegistryArgs
import LIBB_AccountCarriers
import NMX_R2_CallArguments
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryArguments
open Aeneas Aeneas.Std AdapterRw

theorem key (k : solana_pubkey.Pubkey) : NMX_R2_Carrier.key k = NND_Carrier.key k := by
 unfold NMX_R2_Carrier.key NND_Carrier.key
 simp only [LIBB_AccountCarriers.byte]

theorem error (e : solana_program_error.ProgramError) : NMX_R2_Carrier.error e = NND_Carrier.error e := by
 cases e <;> simp only [NMX_R2_Carrier.error,NND_Carrier.error,LIBB_AccountCarriers.word]

theorem account (a : r1_pool_adapter.owned.OwnedAccount) :
 NMX_R2_Carrier.account a = NMX_R3_RegistryCarrier.account a := by
 cases hlen : a.length <;> cases hbytes : a.bytes <;>
 simp only [NMX_R2_Carrier.account,NMX_R3_RegistryCarrier.account,NMX_R2_Carrier.reply,NND_Carrier.reply,
  hlen,hbytes,key,error,NND_Carrier.bytes,LIBB_AccountCarriers.byte]

theorem same (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 NMX_R2_CallArguments.registry v p m s reg ent t = NMX_R3_RegistryArgs.args v p m s reg ent t := by
 simp only [NMX_R2_CallArguments.registry,NMX_R3_RegistryArgs.args,key,account,
  LIBB_AccountCarriers.master,LIBB_AccountCarriers.long]
#print axioms key
#print axioms error
#print axioms account
#print axioms same
end NMX_R3_RegistryArguments
end

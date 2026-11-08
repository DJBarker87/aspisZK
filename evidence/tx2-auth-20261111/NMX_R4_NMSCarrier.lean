import NMX_R4_Authentication
import NMS_R2Parameterized242
import LIBB_AuthCarrier
set_option autoImplicit false
noncomputable section
namespace NMX_R4_NMSCarrier
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets

theorem key (k : solana_pubkey.Pubkey) :
 NMS_R2N_RSLScalars.b32 k = NMX_R2_Carrier.key k :=
 (NMX_R3_RegistryArguments.key k).symm

theorem error (e : PE) : NMS_R2N_RSLError.error e = NMX_R2_Carrier.error e := by
 change NND_Carrier.error e = NMX_R2_Carrier.error e
 exact (NMX_R3_RegistryArguments.error e).symm

theorem account (a : r1_pool_adapter.owned.OwnedAccount) :
 NMS_R2N_RSLPoolCarriers.account a = NMX_R2_Carrier.account a :=
 (NMX_R3_RegistryArguments.account a).symm

theorem accounts : NMS_R2N_RSLPoolCarriers.account = NMX_R2_Carrier.account := funext account

theorem digests : NMX_R2_Carrier.digest = NND_Carrier.digest := by
 funext d
 simp only [NMX_R2_Carrier.digest,NND_Carrier.digest,LIBB_AccountCarriers.word]

theorem args (v : solana_pubkey.Pubkey) (as_ : Slice r1_pool_adapter.owned.OwnedAccount)
 (pool : solana_pubkey.Pubkey) (lane : U8) (slot : U64) :
 NMS_R2N_RSLPoolCarriers.args233 v as_ pool lane slot =
 (⟨NMX_R2_Carrier.key v,as_.val.map NMX_R2_Carrier.account,NMX_R2_Carrier.key pool,
  NMX_R2_Carrier.byte lane,NMX_R2_Carrier.long slot⟩ : RSL.TX2_233.Args) := by
 simp only [NMS_R2N_RSLPoolCarriers.args233,NMS_R2N_RSLPoolCarriers.accounts,key,accounts,
  LIBB_AccountCarriers.byte,LIBB_AccountCarriers.long]
 rfl

theorem auth (a : Auth) :
 NMS_R2N_RSLPoolCarriers.authenticated a.erase = NMX_R2_Carrier.auth a := by
 rw [LIBB_AuthCarrier.exact_carrier]
 simp only [NND_Carrier.auth,Auth.erase,NMX_R2_Carrier.auth,
   LIBB_AccountCarriers.master,LIBB_AccountCarriers.checkpoint,NMX_R3_RegistryArguments.key,
   NMX_R2_Carrier.lane,NMX_R2_Carrier.tree,NMX_R2_Carrier.snapshot,NMX_R2_Carrier.digest,
   NMX_R2_Carrier.key,NND_Carrier.lane,NND_Carrier.tree,NND_Carrier.live,NND_Carrier.digest,
   NND_Carrier.frontier,NND_Carrier.key,LIBB_AccountCarriers.byte,LIBB_AccountCarriers.word,
   LIBB_AccountCarriers.long,digests]

#print axioms key
#print axioms error
#print axioms account
#print axioms accounts
#print axioms digests
#print axioms args
#print axioms auth
end NMX_R4_NMSCarrier
end

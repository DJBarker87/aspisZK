import NMS_242First
set_option autoImplicit false
noncomputable section
namespace NMS_242Auth
open Aeneas Aeneas.Std AdapterRw NMS_OwnedPackets NMS_RowSpec242

def owned {Ambient : Type} (ops : Ops) (child : NMS_RowSpec233.Native Ambient)
 (before : World Ambient) (inputs : List Nat) (request : Request)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (pool : solana_pubkey.Pubkey) (lane : U8) (slot : U64) :
 NMS_Owned242.Run Ambient (NMS_TryFold.R Validated) :=
 NMS_TryFold.step (NMS_Owned242.authenticate child before program accounts pool lane slot)
  (fun auth => NMS_242First.owned ops inputs request auth accounts)

def raw (ops : Ops) (request : Request) (program : solana_pubkey.Pubkey)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey)
 (lane : U8) (slot : U64) : NJU_Log.Run RawEvent (NMS_TryFold.R r1_pool_adapter.ValidatedAsqa) :=
 NMS_TryFold.step (NLM_Validate242.authenticate ops program accounts pool lane slot)
  (fun auth => NMS_242First.raw ops request auth accounts)

theorem erases {Ambient CoreError : Type}
 (missing : AspisR1.IDa_Deployed.Uninstalled CoreError) (indexError : CoreError)
 (reservation : AspisR1.NP6_StdModel.Reservation)
 (owners : NMS_RowSpec233.Args → List Nat) (native : NMS_RowSpec233.Native Ambient)
 (packet : NMS_RowSpec233.RowSpec_233 missing indexError reservation owners native)
 (before : World Ambient) (inputs : List Nat) (request : Request)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (pool : solana_pubkey.Pubkey) (lane : U8) (slot : U64) :
 NMS_LogMap.run Event.erase (NMS_LogMap.rust Validated.erase)
  (owned (NLM_DeployedOps.ops missing indexError reservation) native before inputs request
   program accounts pool lane slot) =
 raw (NLM_DeployedOps.ops missing indexError reservation) request program accounts pool lane slot := by
 unfold owned raw
 apply NMS_TryFold.mapped Event.erase Auth.erase Validated.erase
 · exact NMS_Owned242Cuts.authenticate missing indexError reservation owners native packet
    before program accounts pool lane slot
 · intro auth
   exact NMS_242First.erases _ inputs request auth accounts
#print axioms erases
end NMS_242Auth

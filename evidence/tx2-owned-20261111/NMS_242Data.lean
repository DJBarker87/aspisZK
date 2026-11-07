import NMS_242Scan
import NMS_PlainMap
set_option autoImplicit false
noncomputable section
namespace NMS_242Data
open Aeneas Aeneas.Std AdapterRw NMS_OwnedPackets NMS_RowSpec242

def owned {Ambient : Type} (ops : Ops) (inputs : List Nat)
 (request : Request) (auth : Auth) (account : r1_pool_adapter.owned.OwnedAccount) :
 NMS_Owned242.Run Ambient (NMS_TryFold.R Validated) :=
 NMS_TryFold.step
  (NJU_Log.record (fun reply => Event.plain (NLM_Validate242.Event.data account reply) (by trivial))
   (r1_pool_adapter.owned.OwnedAccount.data ops account))
  (NMS_242Scan.owned ops inputs request auth)

def raw (ops : Ops) (request : Request) (auth : r1_pool_adapter.AuthenticatedAsq8Accounts)
 (account : r1_pool_adapter.owned.OwnedAccount) :
 NJU_Log.Run RawEvent (NMS_TryFold.R r1_pool_adapter.ValidatedAsqa) :=
 NMS_TryFold.step
  (NJU_Log.record (NLM_Validate242.Event.data account)
   (r1_pool_adapter.owned.OwnedAccount.data ops account))
  (NMS_242Scan.raw ops request auth)

theorem erases {Ambient : Type} (ops : Ops) (inputs : List Nat)
 (request : Request) (auth : Auth) (account : r1_pool_adapter.owned.OwnedAccount) :
 NMS_LogMap.run (Event.erase (Ambient := Ambient)) (NMS_LogMap.rust Validated.erase)
  (owned ops inputs request auth account) = raw ops request auth.erase account := by
 unfold owned raw
 apply NMS_TryFold.mapped Event.erase id Validated.erase
 · exact NMS_PlainMap.record_rust (NLM_Validate242.Event.data account) (fun _ => by trivial) _
 · intro bytes
   exact NMS_242Scan.erases ops inputs request auth bytes
#print axioms erases
end NMS_242Data

import NMS_242Tail
set_option autoImplicit false
noncomputable section
namespace NMS_242Scan
open Aeneas Aeneas.Std AdapterRw NMS_OwnedPackets NMS_RowSpec242

def owned {Ambient : Type} (ops : Ops) (inputs : List Nat)
 (request : Request) (auth : Auth) (bytes : Slice U8) :
 NMS_Owned242.Run Ambient (NMS_TryFold.R Validated) :=
 NMS_TryFold.step (NMS_Owned242.scan ops inputs auth bytes)
  (NMS_242Tail.owned ops inputs request auth)

def raw (ops : Ops) (request : Request)
 (auth : r1_pool_adapter.AuthenticatedAsq8Accounts) (bytes : Slice U8) :
 NJU_Log.Run RawEvent (NMS_TryFold.R r1_pool_adapter.ValidatedAsqa) :=
 NMS_TryFold.step (NJU_Log.record (NLM_Validate242.Event.scan bytes) (ops.op51 bytes))
  (NMS_242Tail.raw ops request auth)

theorem erases {Ambient : Type} (ops : Ops) (inputs : List Nat)
 (request : Request) (auth : Auth) (bytes : Slice U8) :
 NMS_LogMap.run (Event.erase (Ambient := Ambient)) (NMS_LogMap.rust Validated.erase)
  (owned ops inputs request auth bytes) = raw ops request auth.erase bytes := by
 unfold owned raw
 apply NMS_TryFold.mapped Event.erase Scanned.erase Validated.erase
 · exact NMS_Owned242Cuts.scan ops inputs auth bytes
 · intro scanned
   exact NMS_242Tail.erases ops inputs request auth scanned
#print axioms erases
end NMS_242Scan

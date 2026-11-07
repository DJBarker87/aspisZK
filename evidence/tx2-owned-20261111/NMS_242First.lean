import NMS_242Data
set_option autoImplicit false
noncomputable section
namespace NMS_242First
open Aeneas Aeneas.Std AdapterRw NMS_OwnedPackets NMS_RowSpec242

def owned {Ambient : Type} (ops : Ops) (inputs : List Nat)
 (request : Request) (auth : Auth) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) :
 NMS_Owned242.Run Ambient (NMS_TryFold.R Validated) := do
 let first ← ops.op9 accounts
 NMS_TryFold.step
  (liftM (core.option.Option.ok_or first solana_program_error.ProgramError.NotEnoughAccountKeys))
  (NMS_242Data.owned ops inputs request auth)

def raw (ops : Ops) (request : Request) (auth : r1_pool_adapter.AuthenticatedAsq8Accounts)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) :
 NJU_Log.Run RawEvent (NMS_TryFold.R r1_pool_adapter.ValidatedAsqa) := do
 let first ← ops.op9 accounts
 NMS_TryFold.step
  (liftM (core.option.Option.ok_or first solana_program_error.ProgramError.NotEnoughAccountKeys))
  (NMS_242Data.raw ops request auth)

theorem erases {Ambient : Type} (ops : Ops) (inputs : List Nat)
 (request : Request) (auth : Auth) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) :
 NMS_LogMap.run (Event.erase (Ambient := Ambient)) (NMS_LogMap.rust Validated.erase)
  (owned ops inputs request auth accounts) = raw ops request auth.erase accounts := by
 unfold owned raw
 apply NMS_TryFold.lift_bind
 intro first
 apply NMS_TryFold.mapped Event.erase id Validated.erase
 · exact NMS_PlainMap.lift_rust _
 · intro account
   exact NMS_242Data.erases ops inputs request auth account
#print axioms erases
end NMS_242First

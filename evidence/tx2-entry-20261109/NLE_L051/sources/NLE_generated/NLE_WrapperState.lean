import NLE_OwnedState
set_option autoImplicit false
noncomputable section
namespace NLE_Wrapper
open Aeneas Aeneas.Std Result
abbrev PE := NLE_Owned.PE
abbrev Owned := NLE_Owned.Account
abbrev Key := AdapterRw.solana_pubkey.Pubkey
abbrev PR := NLE_Owned.PR
structure Frame (Account : Type) where
 program : Key
 accounts : Slice Account
 data : Slice U8
structure State (Account : Type) where
 frame : Frame Account
 snapshots : List Owned := []
 slot : Option (core.result.Result U64 PE) := none
inductive Event (Account : Type) where
 | header (state : State Account) (reply : Result Bool)
 | clear (state : State Account) (bytes : Slice U8) (reply : Result Unit)
 | snapshot (state : State Account) (index : Usize) (account : Account)
   (min max : Usize) (reply : Result Owned)
 | clock (state : State Account) (reply : Result (core.result.Result U64 PE))
 | child (state : State Account) (owned : Array Owned 7#usize)
   (slot : core.result.Result U64 PE) (reply : Result PR)
/-- Intermediate boundary data only. Every field still requires its complete
CLOSED native packet; this dictionary is not permitted at a row root. -/
structure Ops (Account : Type) where
 header : Slice Account → Slice U8 → Result Bool
 clear : Slice U8 → Result Unit
 snapshot : Account → Usize → Usize → Result Owned
 clock : Result (core.result.Result U64 PE)
 child : Key → Slice Owned → Slice U8 → core.result.Result U64 PE → Result PR
abbrev Run (Account A : Type) := NJU_Log.Run (Event Account) A
/-- RuntimeReturnDataClear receives exactly the empty byte slice. -/
def clear {Account : Type} (ops : Ops Account) (state : State Account) : Run Account Unit :=
 let empty : Slice U8 := ⟨[],by simp⟩
 NJU_Log.record (.clear state empty) (ops.clear empty)
def snapshot {Account : Type} (ops : Ops Account) (state : State Account)
 (index min max : Usize) : Run Account (Owned × State Account) := do
 let account ← liftM (state.frame.accounts.index_usize index)
 let value ← NJU_Log.record (.snapshot state index account min max) (ops.snapshot account min max)
 pure (value,{state with snapshots := state.snapshots ++ [value]})
end NLE_Wrapper

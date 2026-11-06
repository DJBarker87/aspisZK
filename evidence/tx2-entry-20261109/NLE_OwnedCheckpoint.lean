import NLE_OwnedProof
set_option autoImplicit false
noncomputable section
namespace NLE_OwnedStep
open Aeneas Aeneas.Std Result AdapterRw NLE_Owned
/-- Source occurrence only: complete typed reply on the SAME arguments.
Native cut and callee-domain installation remain independent obligations. -/
def checkpoint (ops : Ops) (state : State) (account : Account) : Run (core.result.Result (Slice U8) PE) :=
 NJU_Log.record (.checkpoint state account) ((r1_pool_adapter.owned.OwnedAccount.data ops) account)
theorem checkpoint_result (ops : Ops) (state : State) (account : Account) :
 (checkpoint ops state account).result = (r1_pool_adapter.owned.OwnedAccount.data ops) account := rfl
theorem checkpoint_events (ops : Ops) (state : State) (account : Account) :
 (checkpoint ops state account).events = [Event.checkpoint state account ((r1_pool_adapter.owned.OwnedAccount.data ops) account)] := rfl
#print checkpoint_result
#print axioms checkpoint_result
#print axioms checkpoint_events
end NLE_OwnedStep

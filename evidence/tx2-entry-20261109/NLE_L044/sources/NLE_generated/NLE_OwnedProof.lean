import NLE_OwnedValidate
set_option autoImplicit false
noncomputable section
namespace NLE_OwnedStep
open Aeneas Aeneas.Std Result AdapterRw NLE_Owned
/-- Source occurrence only: complete typed reply on the SAME arguments.
Native cut and callee-domain installation remain independent obligations. -/
def proof (ops : Ops) (state : State) (account : Account) : Run (core.result.Result (Slice U8) PE) :=
 NJU_Log.record (.proof state account) ((r1_pool_adapter.owned.OwnedAccount.data ops) account)
theorem proof_result (ops : Ops) (state : State) (account : Account) :
 (proof ops state account).result = (r1_pool_adapter.owned.OwnedAccount.data ops) account := rfl
theorem proof_events (ops : Ops) (state : State) (account : Account) :
 (proof ops state account).events = [Event.proof state account ((r1_pool_adapter.owned.OwnedAccount.data ops) account)] := rfl
#print proof_result
#print axioms proof_result
#print axioms proof_events
end NLE_OwnedStep

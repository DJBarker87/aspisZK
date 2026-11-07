import NLE_OwnedState
set_option autoImplicit false
noncomputable section
namespace NLE_OwnedStep
open Aeneas Aeneas.Std Result AdapterRw NLE_Owned
/-- Source occurrence only: complete typed reply on the SAME arguments.
Native cut and callee-domain installation remain independent obligations. -/
def validate (ops : Ops) (state : State) : Run (core.result.Result Validated PE) :=
 NJU_Log.record (.validate state) ((r1_pool_adapter.owned.validate_asq8 ops) state.frame.program state.frame.accounts state.frame.data state.frame.slot)
theorem validate_result (ops : Ops) (state : State) :
 (validate ops state).result = (r1_pool_adapter.owned.validate_asq8 ops) state.frame.program state.frame.accounts state.frame.data state.frame.slot := rfl
theorem validate_events (ops : Ops) (state : State) :
 (validate ops state).events = [Event.validate state ((r1_pool_adapter.owned.validate_asq8 ops) state.frame.program state.frame.accounts state.frame.data state.frame.slot)] := rfl
#print validate_result
#print axioms validate_result
#print axioms validate_events
end NLE_OwnedStep

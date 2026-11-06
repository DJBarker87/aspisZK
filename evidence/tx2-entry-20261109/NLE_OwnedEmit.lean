import NLE_OwnedEncode
set_option autoImplicit false
noncomputable section
namespace NLE_OwnedStep
open Aeneas Aeneas.Std Result AdapterRw NLE_Owned
/-- Source occurrence only: complete typed reply on the SAME arguments.
Native cut and callee-domain installation remain independent obligations. -/
def emit (ops : Ops) (state : State) (statement : Statement) : Run (PR) :=
 NJU_Log.record (.emit state statement) (ops.op53 statement)
theorem emit_result (ops : Ops) (state : State) (statement : Statement) :
 (emit ops state statement).result = ops.op53 statement := rfl
theorem emit_events (ops : Ops) (state : State) (statement : Statement) :
 (emit ops state statement).events = [Event.emit state statement (ops.op53 statement)] := rfl
#print emit_result
#print axioms emit_result
#print axioms emit_events
end NLE_OwnedStep

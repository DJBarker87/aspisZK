import NLE_OwnedCheckpoint
set_option autoImplicit false
noncomputable section
namespace NLE_OwnedStep
open Aeneas Aeneas.Std Result AdapterRw NLE_Owned
/-- Source occurrence only: complete typed reply on the SAME arguments.
Native cut and callee-domain installation remain independent obligations. -/
def encode (ops : Ops) (state : State) (statement : Statement) : Run (core.result.Result (Array U8 1880#usize) aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) :=
 NJU_Log.record (.encode state statement) (ops.op22 statement)
theorem encode_result (ops : Ops) (state : State) (statement : Statement) :
 (encode ops state statement).result = ops.op22 statement := rfl
theorem encode_events (ops : Ops) (state : State) (statement : Statement) :
 (encode ops state statement).events = [Event.encode state statement (ops.op22 statement)] := rfl
#print encode_result
#print axioms encode_result
#print axioms encode_events
end NLE_OwnedStep

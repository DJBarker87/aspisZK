import R1Z.PV_Src_PortConstantInstance
import R1Z.PV_Src_PortTraceCanonical

set_option autoImplicit false
namespace R1Z.PV_Src_PortNoop
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort
abbrev callback := poseidon2.merkle_node_compress_v3.closure.Insts.CoreOpsFunctionFnMutTuplePoseidon2RoundTransitionTuple

theorem call (trace : Unit) (event : poseidon2.Poseidon2RoundTransition) :
    callback.call_mut trace event = ok ((),trace) := rfl

#print axioms call
end R1Z.PV_Src_PortNoop

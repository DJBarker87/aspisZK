import NNG_Packet136
import NNG_DRowSpec136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Candidate136

/-- Complete emitted-body candidate at LIB's concrete VL-star. All opaque
children are installed from their CLOSED deterministic models at the actual
entered arguments. No child/library/trace packet parameter remains. -/
theorem candidate : RSL.TX1_136.RowSpec_136 LIB_VLib.library NNG_Producer136.producer :=
  NNG_DRowSpec136.fold LIB_VLib.library NNG_Representation136.project NNG_Representation136.calls
    NNG_Representation136.input NNG_Producer136.events NNG_Packet136.closed
#print axioms candidate
end AspisR1.NNG_Candidate136

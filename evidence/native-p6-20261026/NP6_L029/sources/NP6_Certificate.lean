import NP6_ParsedPair
import NP6_ResultBridge
import NP6_StdBridge
import NP6_Initialization

/-! Final focused audit of the P6 proof closure. Rust source instances are
recorded by the Kani/source certificate; they are not Lean axioms. This audit
does not assert global S2 or release security. -/
#print axioms AspisR1.NP6_ParsedPair.accepted_pair_unified
#print axioms AspisR1.NP6_ResultBridge.complete_result
#print axioms AspisR1.NP6_StdBridge.allocation_failure
#print axioms AspisR1.NP6_StdBridge.map_error
#print axioms AspisR1.NP6_StdBridge.box_array_contents
#print axioms AspisR1.NP6_Initialization.complete
#print axioms AspisR1.NP6_StdModel.reserve_contents
#print axioms AspisR1.NP6_StdModel.box_contents
#print axioms AspisR1.NP6_Constructors.on_run
#print axioms AspisR1.NP6_Constructors.local_nonvacuity
#print axioms AspisR1.NP6_ParsedClaims.on_success

import R1Z.PV_ROWS10_Combined
import R1Z.PV_ROWS10_Audit
set_option autoImplicit false
namespace R1Z.PV_ROWS10_Replay
open PV_ROWS10_Entropy
/-- Tiny boundary negative control: error does not erase the boundary's writes. -/
theorem error_buffer : buffer (run [.error 1 [3]] [9] []) = [3] := rfl
#print axioms error_buffer
#check PV_ROWS10_Combined.local_results
#check PV_ROWS10_Entropy.consumed_signal
#check PV_ROWS10_WorkRanges.intermediate_bounds
end R1Z.PV_ROWS10_Replay

-- Focused source factoring of the generated COPY_PATTERNS declaration.
import Aeneas
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.FunsExternal
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AspisR1SelectedMaskProbe

namespace pool_v1.pair_forest_copy_terminal.constants
/-- Factored from the exact local let-bindings in generated COPY_PATTERNS. -/
def copyPatternsKindsOnes : Array Std.U8 16#usize := Array.repeat 16#usize 1#u8
def copyPatternsZeroU8 : Array Std.U8 16#usize := Array.repeat 16#usize 0#u8
def copyPatternsZeroU32 : Array Std.U32 16#usize := Array.repeat 16#usize 0#u32
end pool_v1.pair_forest_copy_terminal.constants
end AspisR1SelectedMaskProbe

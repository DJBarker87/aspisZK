import TerminalV4CopyPatternsRows01V1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AspisR1SelectedMaskProbe
namespace pool_v1.pair_forest_copy_terminal.constants
def copyPattern_01_sourceKinds : Array Std.U8 16#usize := Array.make 16#usize [
  1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8,
  0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8
]
theorem copyPattern_01_sourceKinds_eq : copyPattern_01_sourceKinds = copyPattern_01.kinds := by rfl
end pool_v1.pair_forest_copy_terminal.constants
end AspisR1SelectedMaskProbe

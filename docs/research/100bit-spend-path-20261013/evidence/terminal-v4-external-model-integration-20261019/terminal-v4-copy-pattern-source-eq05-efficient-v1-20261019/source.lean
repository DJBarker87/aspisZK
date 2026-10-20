import TerminalV4CopyPatternsRows01V1
import TerminalV4CopyPatternFieldExtV1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AspisR1SelectedMaskProbe
namespace pool_v1.pair_forest_copy_terminal.constants
def copyPattern_05_source : pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern :=
  (let a6 := Array.repeat 16#usize 0#u32;     {
      kinds :=
        (Array.make 16#usize [
          1#u8, 1#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      columns :=
        (Array.make 16#usize [
          6#u8, 7#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      offsets := a6
    })
theorem copyPattern_05_source_eq_factored : copyPattern_05_source = copyPattern_05 := by
  apply copyPattern_ext_fields <;> rfl
end pool_v1.pair_forest_copy_terminal.constants
end AspisR1SelectedMaskProbe

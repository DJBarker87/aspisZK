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
def copyPattern_00_source : pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern :=
  (let a := Array.repeat 16#usize 1#u8; let a1 := Array.repeat 16#usize 0#u32;     {
      kinds := a,
      columns :=
        (Array.make 16#usize [
          0#u8, 1#u8, 2#u8, 3#u8, 4#u8, 5#u8, 6#u8, 7#u8, 8#u8, 9#u8, 10#u8,
          11#u8, 12#u8, 13#u8, 14#u8, 15#u8
          ]),
      offsets := a1
    })
theorem copyPattern_00_source_eq_factored : copyPattern_00_source = copyPattern_00 := by
  apply copyPattern_ext_fields <;> rfl
end pool_v1.pair_forest_copy_terminal.constants
end AspisR1SelectedMaskProbe

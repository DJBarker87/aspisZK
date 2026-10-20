-- Focused source factoring of the generated COPY_PATTERNS declaration.
import Aeneas
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.FunsExternal
import TerminalV4CopyPatternsSupportV1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AspisR1SelectedMaskProbe

namespace pool_v1.pair_forest_copy_terminal.constants

def copyPattern_00 : pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern :=
    {
      kinds := copyPatternsKindsOnes,
      columns :=
        (Array.make 16#usize [
          0#u8, 1#u8, 2#u8, 3#u8, 4#u8, 5#u8, 6#u8, 7#u8, 8#u8, 9#u8, 10#u8,
          11#u8, 12#u8, 13#u8, 14#u8, 15#u8
          ]),
      offsets := copyPatternsZeroU32
    }


end pool_v1.pair_forest_copy_terminal.constants
end AspisR1SelectedMaskProbe

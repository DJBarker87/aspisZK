-- Focused source factoring of the generated COPY_PATTERNS declaration.
import Aeneas
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.FunsExternal
import TerminalV4CopyPatternsRows01V1
import TerminalV4CopyPatternsRows02V1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AspisR1SelectedMaskProbe

namespace pool_v1.pair_forest_copy_terminal.constants
@[irreducible]
def COPY_PATTERNS : Array pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern 14#usize :=
  Array.make 14#usize [
    pool_v1.pair_forest_copy_terminal.constants.copyPattern_00,
    pool_v1.pair_forest_copy_terminal.constants.copyPattern_01,
    pool_v1.pair_forest_copy_terminal.constants.copyPattern_02,
    pool_v1.pair_forest_copy_terminal.constants.copyPattern_03,
    pool_v1.pair_forest_copy_terminal.constants.copyPattern_04,
    pool_v1.pair_forest_copy_terminal.constants.copyPattern_05,
    pool_v1.pair_forest_copy_terminal.constants.copyPattern_06,
    pool_v1.pair_forest_copy_terminal.constants.copyPattern_07,
    pool_v1.pair_forest_copy_terminal.constants.copyPattern_08,
    pool_v1.pair_forest_copy_terminal.constants.copyPattern_09,
    pool_v1.pair_forest_copy_terminal.constants.copyPattern_10,
    pool_v1.pair_forest_copy_terminal.constants.copyPattern_11,
    pool_v1.pair_forest_copy_terminal.constants.copyPattern_12,
    pool_v1.pair_forest_copy_terminal.constants.copyPattern_13
  ]
end pool_v1.pair_forest_copy_terminal.constants
end AspisR1SelectedMaskProbe

import TerminalV4CopyPatternsFactoredV1
import TerminalV4CopyPatternSourceEq00V1
import TerminalV4CopyPatternSourceEq01ByFieldsV2
import TerminalV4CopyPatternSourceEq02V1
import TerminalV4CopyPatternSourceEq03V1
import TerminalV4CopyPatternSourceEq04V1
import TerminalV4CopyPatternSourceEq05V1
import TerminalV4CopyPatternSourceEq06V1
import TerminalV4CopyPatternSourceEq07V1
import TerminalV4CopyPatternSourceEq08V1
import TerminalV4CopyPatternSourceEq09V1
import TerminalV4CopyPatternSourceEq10V1
import TerminalV4CopyPatternSourceEq11V1
import TerminalV4CopyPatternSourceEq12V1
import TerminalV4CopyPatternSourceEq13V1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.constants
def sourceCopyPatterns : Array AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern 14#usize :=
  Array.make 14#usize [
    copyPattern_00_source,
    copyPattern_01_source,
    copyPattern_02_source,
    copyPattern_03_source,
    copyPattern_04_source,
    copyPattern_05_source,
    copyPattern_06_source,
    copyPattern_07_source,
    copyPattern_08_source,
    copyPattern_09_source,
    copyPattern_10_source,
    copyPattern_11_source,
    copyPattern_12_source,
    copyPattern_13_source
  ]
theorem sourceCopyPatterns_eq_COPY_PATTERNS : sourceCopyPatterns = COPY_PATTERNS := by
  unfold sourceCopyPatterns COPY_PATTERNS
  simp only [copyPattern_00_source_eq_factored, copyPattern_01_source_eq_factored, copyPattern_02_source_eq_factored, copyPattern_03_source_eq_factored, copyPattern_04_source_eq_factored, copyPattern_05_source_eq_factored, copyPattern_06_source_eq_factored, copyPattern_07_source_eq_factored, copyPattern_08_source_eq_factored, copyPattern_09_source_eq_factored, copyPattern_10_source_eq_factored, copyPattern_11_source_eq_factored, copyPattern_12_source_eq_factored, copyPattern_13_source_eq_factored]
#print axioms sourceCopyPatterns_eq_COPY_PATTERNS
end AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.constants

import TerminalV4CopyPatternsRows01V1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.constants
 theorem copyPattern_ext_fields {a b : AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern}
   (hk : a.kinds = b.kinds) (hc : a.columns = b.columns) (ho : a.offsets = b.offsets) : a = b := by
   cases a with
   | mk ak ac ao =>
     cases b with
     | mk bk bc bo =>
       simp_all
end AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.constants

import NKI_LevelsComplete
import NKP_BoxCuts
open Lean Elab Command
run_cmd do
 for (n, _) in (← getEnv).constants.toList do
  if n.toString.endsWith "append_levels_packed_selector_tensor" || n.toString.endsWith "append_level_packed_selector_tensor" then
   elabCommand (← `(command| #print $(mkIdent n)))

import NIU_COMBINED_IMPORT
import NGK_COMBINED_IMPORT
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for (n, _) in env.constants.toList do
  let s := n.toString
  if (s.startsWith "AspisR1.FIv_NativeValue." || s.startsWith "AspisR1.FIv_NativeArithmetic." || s.startsWith "AspisR1.JFy_CopyResidual") then
   logInfo m!"{n}"

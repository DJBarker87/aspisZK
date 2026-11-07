import LIB_COMBINED_IMPORT
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for name in env.header.moduleNames do
  logInfo m!"LIB_SELECTED_MODULE {name}"

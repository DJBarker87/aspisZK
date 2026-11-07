import LIB_FINAL_IMPORT
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for n in env.header.moduleNames do
  logInfo m!"LIB_SELECTED_MODULE {n}"

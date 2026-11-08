import NNN_COMBINED_IMPORT
import Lean
open Lean Elab Command
set_option pp.all true
run_cmd do
 let roots := #[`FIN_240.candidate, `FIN_333.candidate, `FIN_221.candidate,
  `FIN_330.candidate, `FIN_213.candidate,
  `NNN_InstalledChecks.f344_same, `NNN_InstalledChecks.f240_same,
  `NNN_InstalledChecks.process_same, `NNN_InstalledChecks.entry_same]
 let env := (← getEnv).setExporting false
 for root in roots do
  let some c := env.find? root | throwError "missing root {root}"
  let some idx := env.getModuleIdxFor? root | throwError "missing owner {root}"
  let statement ← liftTermElabM (PrettyPrinter.ppExpr c.type)
  let row := Json.mkObj [("root",toJson root.toString),
   ("owner_module",toJson env.header.moduleNames[idx]!.toString),
   ("obligation_statement",toJson statement.pretty)]
  logInfo m!"NNN_OWNER {row.compress}"

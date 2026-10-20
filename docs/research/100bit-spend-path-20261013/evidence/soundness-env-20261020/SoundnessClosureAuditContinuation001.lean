import Lean
import Stage2FirstMatch
import Stage2FinishSourceFacts
import Stage2FinishChecks
import Stage2FinishReducer
import Stage2FinishAudit
import WireTx2ResumeCalls
import WireTx2Carrier

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`Stage2FirstMatch, `Stage2FinishSourceFacts, `Stage2FinishChecks, `Stage2FinishReducer, `Stage2FinishAudit, `WireTx2ResumeCalls, `WireTx2Carrier]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"

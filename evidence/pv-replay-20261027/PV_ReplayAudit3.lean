import R1Z.PrivacyR1HeadlineDeployedReal
import R1Z.PrivacyR1HeadlineV2
import Lean.Elab.Command

/- Diagnostic only: print accepted axioms for every theorem in every imported
   R1Z or PV module, including both headline theorems. No proof is changed. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for i in [:env.header.moduleData.size] do
    let mod := env.header.moduleNames[i]!
    let deps := (env.header.moduleData[i]!.imports.toList.map fun imp => imp.module.toString)
    logInfo m!"PV_REPLAY_IMPORT {mod} : {String.intercalate "," deps}"
  logInfo m!"PV_REPLAY_IMPORTED_MODULE_COUNT {env.header.modules.size}"
  let names : List (Name × Name) := env.constants.toList.filterMap fun entry =>
    let declName := entry.1
    let ci := entry.2
    match ci with
    | .thmInfo _ =>
      match env.getModuleIdxFor? declName with
      | some idx =>
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString.startsWith "R1Z." || mod.toString.startsWith "PV_" then
          some (declName, mod)
        else none
      | none => none
    | _ => none
  let names := names.toArray.qsort fun (a b : Name × Name) => Name.quickLt a.1 b.1
  for entry in names do
    let declName := entry.1
    let mod := entry.2
    logInfo m!"PV_REPLAY_MODULE {mod} DECL {declName}"
    elabCommand (← `(command| #print axioms $(mkIdent declName)))
    for ax in (← Lean.collectAxioms declName) do
      if ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound then
        let owner := match env.getModuleIdxFor? ax with
          | some idx => env.header.moduleNames[idx.toNat]!.toString
          | none => "unknown"
        logInfo m!"PV_REPLAY_NONSTANDARD {ax} MODULE {owner} VIA {declName}"
  logInfo m!"PV_REPLAY_THEOREM_COUNT {names.size}"

#check R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed
#check R1Z.PrivacyR1HeadlineDeployedReal.RustRealRefinement
#check R1Z.ProverCommitFuelJoin22.RunJoin
#check R1Z.PrivacyR1HeadlineV2.privacy_headline_v2
#check R1Z.PrivacyR1HeadlineV2.privacy_headline_v2_fibres
#print axioms R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed
#print axioms R1Z.PrivacyR1HeadlineV2.privacy_headline_v2
#print axioms R1Z.PrivacyR1HeadlineV2.privacy_headline_v2_fibres

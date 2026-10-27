import R1Z.PrivacyR1HeadlineDeployedReal
import R1Z.PrivacyR1HeadlineV2
import Lean.Elab.Command

/- Diagnostic only: print accepted axioms for every theorem in every imported
   R1Z or PV module, including both headline theorems. No proof is changed. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, ci) =>
    match ci with
    | .thmInfo _ =>
      match env.getModuleIdxFor? name with
      | some idx =>
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString.startsWith "R1Z." || mod.toString.startsWith "PV_" then
          some (name, mod)
        else none
      | none => none
    | _ => none
  let names := names.toArray.qsort fun a b => Name.quickLt a.1 b.1
  for (name, mod) in names do
    logInfo m!"PV_REPLAY_MODULE {mod} DECL {name}"
    elabCommand (← `(command| #print axioms $(mkIdent name)))
    for ax in (← Lean.collectAxioms name) do
      if ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound then
        let owner := match env.getModuleIdxFor? ax with
          | some idx => env.header.moduleNames[idx.toNat]!.toString
          | none => "unknown"
        logInfo m!"PV_REPLAY_NONSTANDARD {ax} MODULE {owner} VIA {name}"
  logInfo m!"PV_REPLAY_THEOREM_COUNT {names.size}"

#check R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed
#check R1Z.PrivacyR1HeadlineDeployedReal.RustRealRefinement
#check R1Z.ProverCommitFuelJoin22.RunJoin
#check R1Z.PrivacyR1HeadlineV2.privacy_headline_v2
#check R1Z.PrivacyR1HeadlineV2.privacy_headline_v2_fibres
#print axioms R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed
#print axioms R1Z.PrivacyR1HeadlineV2.privacy_headline_v2
#print axioms R1Z.PrivacyR1HeadlineV2.privacy_headline_v2_fibres

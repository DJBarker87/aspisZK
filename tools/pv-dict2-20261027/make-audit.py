from pathlib import Path
import json
E=Path('evidence/pv-dict2-20261027');t=json.loads((E/'TALLY.json').read_text());mods=list(dict.fromkeys(a['module'] for a in t['attempts'] if a.get('exit')==0));assert mods
plan=json.loads((E/'closure-plan.json').read_text());missing=[m for m in plan['roots'] if m not in mods]
path=Path('docs/research/v8-r0-zk-20261009/lean/R1Z/PV_Dict2_Audit.lean')
s='\n'.join('import '+m for m in mods)+'\nimport Lean\nopen Lean Elab Command\n#print axioms ProverRwFull.ExternalFuns\n'
s+='''run_cmd do
  let env ← getEnv
  for moduleName in env.header.moduleNames do
    logInfo m!"MODULE|{moduleName}"
  for (n, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let owner := env.header.moduleNames[idx]!
      let text := owner.toString
      if text.startsWith "R1Z.PDict_" || text == "R1Z.PV_CB_Op229Transport" ||
          text == "R1Z.PV_CB_PathBorrow" || text == "R1Z.PV_CB_ArrayCarrierObstruction" ||
          text == "R1Z.PV_Join_DictInspect" || text == "R1Z.PV_Join_Op20Value" then
        logInfo m!"OWNER|{owner}|{n}"
        elabCommand (← `(command| #print axioms $(mkIdent n)))
'''
path.write_text(s);(E/'audit-scope.json').write_text(json.dumps(dict(imports=mods,requested_roots_not_rechecked=missing,scope='all declarations owned by reachable PDict modules and five direct consumer modules; actual objects pinned in submissions; no coherent frozen replay claim'),indent=2)+'\n');print('audit imports',len(mods),'requested roots not rechecked',missing)

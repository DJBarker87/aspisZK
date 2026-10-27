"""Generate a source/object-pinned Formatter closure audit; no launch logic."""
from pathlib import Path
import hashlib,json,re
base=Path('/home/dombarker/project-offloads/aspis-joint-20261019')
job=Path('/home/dombarker/project-offloads/codex-cx-prover-dict-20261026')
out=job/'formatter262';out.mkdir(exist_ok=True)
roots=['R1Z.PDict_ArrayReference244','R1Z.ProverRwP6BodyData','R1Z.PrivacyR1HeadlineDeployedReal','R1Z.PV_CB3_Afterstate','R1Z.PV_CB3_Op225Source','R1Z.PV_CB3_Op229Source','R1Z.PV_CB3_Op246Source','R1Z.PV_CB3_PoleRows']
seen={}
def visit(mod):
 if mod in seen:return
 src=base/'sources'/(mod.replace('.','/')+'.lean');obj=base/'objects'/(mod.replace('.','/')+'.olean')
 if not src.exists():return
 text=src.read_text();imports=re.findall(r'^import\s+(\S+)',text,re.M)
 seen[mod]=dict(imports=imports,source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),object_sha256=hashlib.sha256(obj.read_bytes()).hexdigest() if obj.exists() else None)
 for child in imports:visit(child)
for root in roots:visit(root)
selected=[m for m in sorted(seen) if m.startswith(('R1Z.PDict_','R1Z.ProverRw','R1Z.PV_CB_','R1Z.PV_CB3_'))]
audit=''.join('import '+m+'\n' for m in roots)+'import Lean\nopen Lean Elab Command\n'
audit+='#print axioms Aeneas.Std.core.fmt.Formatter\n#print axioms ProverRwFull.ExternalFuns\n#print axioms R1Z.ProverRwP6BodyData.refinement_of_data\n'
audit+=''.join(f'#print axioms ProverRwFull.ExternalTypes.op{i}\n' for i in range(28))
audit+='\nrun_cmd do\n  let env ← getEnv\n  for (n, _) in env.constants.toList do\n    if let some idx := env.getModuleIdxFor? n then\n      let owner := env.header.moduleNames[idx]!\n      let text := owner.toString\n      if text.startsWith "R1Z.PDict_" || text.startsWith "R1Z.ProverRw" ||\n          text.startsWith "R1Z.PV_CB_" || text.startsWith "R1Z.PV_CB3_" then\n        logInfo m!"OWNER|{owner}|{n}"\n        elabCommand (← `(command| #print axioms $(mkIdent n)))\n'
(base/'sources/R1Z/PDict_FormatterClosure262.lean').write_text(audit)
(out/'closure-input.json').write_text(json.dumps(dict(roots=roots,audited_modules=selected,modules=seen,qualification='Union of selected dictionary closure, explicit P6 body root, deployed headline, and five CB3 source roots. Does not assert that currently unjoined dictionary/CB roots are instantiated into the headline.'),indent=2)+'\n')
print(len(seen),len(selected))

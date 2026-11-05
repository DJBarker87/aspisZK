from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;U=E.parent/'prepared-claim-20261105'
models=sorted(p.stem for p in E.glob('NGY_*.lean') if 'Driver' not in p.stem and p.stem not in ['NGY_COMBINED_IMPORT','NGY_Statements'])
# Final combined import contains only model modules and the canonical predecessor.
s='import NGK_COMBINED_IMPORT\nimport NGU_PreparedClaim\n'+''.join('import '+m+'\n' for m in models)
owners={}
for m in models:
 t=(E/(m+'.lean')).read_text();ns=re.search(r'^namespace (AspisR1\.NGY_\w+)',t,re.M)
 if ns:
  for n in re.findall(r'^theorem (\w+)',t,re.M):owners[ns[1]+'.'+n]=m
for n in owners:s+='#print axioms '+n+'\n'
s+='#print axioms AspisR1.NGU_PreparedClaim.packet\n#print axioms AspisR1.RPx_Deployed.deployed\n';(E/'NGY_COMBINED_IMPORT.lean').write_text(s)
s='import Lean\nimport NGY_COMBINED_IMPORT\nopen Lean\nset_option pp.universes true\nset_option pp.explicit true\n'
for n,owner in owners.items():
 s+=f'''\n#check @{n}
#print axioms {n}
run_cmd do
 let env ← Lean.getEnv
 let n := `{n}
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `{owner} do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {{entry.compress}}"
'''
(E/'NGY_Statements.lean').write_text(s);(E/'NGY_STATEMENT_ROOTS.json').write_text(json.dumps(owners,indent=1)+'\n')
roots=list(owners)+['AspisR1.NGU_PreparedClaim.packet','AspisR1.RPx_Deployed.deployed']
(E/'NGY_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=[roots]),indent=1)+'\n')
rows={r['module']:r for r in map(json.loads,(U/'NGU_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
for n in ['NCI_KMXFrames','KMX_CopyMeaning']:
 p=E.parents[1]/'lean'/(n+'.lean')
 if n not in rows:rows[n]=dict(module=n,imports=['Init']+list(dict.fromkeys(re.findall(r'^import ([\w.]+)',p.read_text(),re.M))))
for p in E.glob('NGY_*.lean'):rows[p.stem]=dict(module=p.stem,imports=['Init']+list(dict.fromkeys(re.findall(r'^import ([\w.]+)',p.read_text(),re.M))))
(E/'NGY_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(rows[n])+'\n' for n in sorted(rows)))
(E/'NGY_MODULES.json').write_text(json.dumps(models+['NGY_COMBINED_IMPORT'],indent=1)+'\n')
plan=[('lean','NGY_Window'),('lean','NGY_Coverage'),('lean','NGY_Complete'),('lean','NGY_Unified'),('lean','NGY_COMBINED_IMPORT'),('lean','NGY_Statements'),('lean','NGY_ProofDriver'),('lean','NGY_Driver'),('link','NGY_ProofDriver'),('link','NGY_Driver'),('audit','fixtures'),('audit','batch0'),('audit','scan')]
(E/'NGY_PLAN_AUDIT.json').write_text(json.dumps([dict(attempt=f'NGY_L{14+i:03}',kind=k,target=t) for i,(k,t) in enumerate(plan)],indent=1)+'\n')
print(json.dumps(dict(models=len(models),theorems=len(owners),roots=len(roots))))

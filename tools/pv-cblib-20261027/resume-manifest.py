"""Freeze current own-module sources and an explicit declaration axioms manifest."""
from pathlib import Path
import re,json,hashlib,sys,subprocess
root=Path(__file__).resolve().parents[2];b=root/'docs/research/v8-r0-zk-20261009/lean/R1Z';out=root/'evidence/pv-cblib-20261027';rows=json.loads((out/'proof-status.json').read_text())['modules'];reserved={'R1Z/PV_CBL_CallbackAudit','R1Z/PV_CBL_SelectionAudit','R1Z/PV_CBL_FinalManifest'}
assert all(r['status']=='accepted' or r['module'] in reserved for r in rows)
imports=[];names=set();pins=[]
for r in rows:
 if r['module']=='R1Z/PV_CBL_FinalManifest':continue
 p=b/(r['module'].split('/')[-1]+'.lean');s=p.read_text();assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
 imports.append(r['module'].replace('/','.'));pins.append(r)
 ns=re.findall(r'^namespace (\S+)',s,re.M)
 assert len(ns)<=1,p
 for m in re.finditer(r'^(?:@\[[^\n]*\]\s*)?(?:(?:noncomputable|private|protected)\s+)?(?:def|abbrev|theorem|structure|class)\s+([A-Za-z0-9_.]+)',s,re.M):
  assert ns,(p,m[1]);names.add(ns[0]+'.'+m[1])
s='''-- Frozen current-source own-module import and explicit axioms manifest.
-- This does not replay the repository-wide dependency closure or identify deployed execution.
'''+''.join('import '+n+'\n' for n in sorted(imports))+'\n'+''.join('#print axioms '+n+'\n' for n in sorted(names))
p=b/'PV_CBL_FinalManifest.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
r=dict(scope='current own sources and focused accepted objects; inherited dependency-source and deployed association remain open',support_freeze_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),modules=pins,manifest_sha256=hashlib.sha256(s.encode()).hexdigest(),declarations=len(names),imports=len(imports),excluded_diagnostics=[43034,43035],reserved_audit_modules=sorted(reserved))
(out/'manifest-source-pins.json').write_text(json.dumps(r,indent=2)+'\n');print(len(imports),'imports',len(names),'explicit axioms queries')

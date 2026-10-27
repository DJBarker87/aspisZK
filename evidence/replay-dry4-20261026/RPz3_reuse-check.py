"""Read-only validation of inherited fresh object hashes; no prover launch."""
from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];s=json.loads((E/'RPz3_reuse.json').read_text())['state'];inv=json.loads((R/'evidence/replay-dry3-20261026/RPz2_final-object-inventory.json').read_text())['fresh_repository_objects'];expected={}
for m,v in s.items():
 if v=='passed':
  f='RPz_objects/'+m.replace('.','/')+'.olean';expected[f]=inv[f]
payload='''from pathlib import Path
import json,hashlib
B=Path('/home/dombarker/project-offloads/codex-cx-replay-dry-20261026')
expected=json.loads(%r);rows={};bad=[]
for f,want in expected.items():
 p=B/f
 if not p.is_file():bad.append({'path':f,'missing':True});continue
 actual={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size};rows[f]=actual
 if actual!=want:bad.append({'path':f,'expected':want,'actual':actual})
print(json.dumps({'checked':len(rows),'errors':bad,'objects':rows},indent=2))
'''%json.dumps(expected)
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=payload,text=True,capture_output=True);assert r.returncode==0,r.stderr
(E/'RPz3_reuse-check.json').write_text(r.stdout);o=json.loads(r.stdout);print('validated',o['checked'],'errors',len(o['errors']))

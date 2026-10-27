"""Freeze/check the focused source manifest and prepare three joint axioms audits.
This is not a frozen full privacy release or transitive-source replay.
"""
from pathlib import Path
import json,hashlib,re,sys,subprocess
root=Path(__file__).resolve().parents[2];ev=root/'evidence/pv-cb-20261026'
lean=root/'docs/research/v8-r0-zk-20261009/lean'
manifest=ev/'RESUME4-FOCUSED-MANIFEST.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
if '--check' in sys.argv:
 data=json.loads(manifest.read_text())
 for row in data['sources']:assert sha(root/row['path'])==row['sha256'],row['path']
 print('PASS',len(data['sources']),'focused source hashes; no full transitive release claim');sys.exit(0)
assert not manifest.exists()
last={}
for p in sorted(ev.glob('38*.json')):
 if not p.stem.isdigit():continue
 r=json.loads(p.read_text())
 if r.get('exit')==0 and r['module'].split('/')[-1].startswith('PV_CB_'):last[r['module']]=r
rows=[];groups=[[],[],[]]
baseline=json.loads((ev/'27168.json').read_text())
for m,r in sorted(last.items()):
 p=lean/(m+'.lean');assert sha(p)==r['source_sha256'],m
 axioms=[]
 for entry in r.get('axioms',[]):
  name=re.match(r"'([^']+)'",entry)
  assert name and 'sorryAx' not in entry,entry
  axioms.append(name[1])
 assert axioms,m
 group=2 if 'Compress' in m or 'Op223' in m else 1
 groups[group].append((m,axioms))
 rows.append(dict(path=str(p.relative_to(root)),sha256=sha(p),receipt=r['attempt'],axioms=axioms))
groups[0]=[('R1Z/PV_CB_CandidatePublic',[re.match(r"'([^']+)'",a)[1] for a in baseline['axioms']])]
for i,group in enumerate(groups,1):
 p=lean/f'R1Z/PV_CB_Resume4JointAudit{i}.lean';assert not p.exists()
 imports=['import '+m.replace('/','.') for m,_ in group]
 names=sorted(set(a for _,aa in group for a in aa))
 p.write_text('\n'.join(imports)+ '\nset_option autoImplicit false\n'+'\n'.join('#print axioms '+a for a in names)+'\n')
 rows.append(dict(path=str(p.relative_to(root)),sha256=sha(p),role='joint axioms audit',declarations=len(names)))
# Baseline import source identity included; its dependencies remain previously compiled.
p=lean/'R1Z/PV_CB_CandidatePublic.lean'
rows.append(dict(path=str(p.relative_to(root)),sha256=sha(p),receipt=27168,role='prior23-row dictionary; cached transitive dependencies'))
data=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),scope='focused accepted resume4 sources, prior23-row public dictionary and three new audits; direct dependency objects recorded per receipt; not complete frozen privacy manifest',sources=rows)
manifest.write_text(json.dumps(data,indent=2)+'\n')
print('Prepared',len(rows),'focused source entries; audit declaration counts',[len(set(a for _,aa in g for a in aa)) for g in groups])

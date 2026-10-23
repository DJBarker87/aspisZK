#!/usr/bin/env python3
"""Read-only integrity audit of the final sources, snapshots and receipts."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent.parent
L=Path('docs/research/v8-r0-zk-20261009/lean')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((E/'final-manifest.json').read_text())
records={}
for p in (E/'lean').glob('J*.json'):
 r=json.loads(p.read_text());n=int(re.search(r'J(\d+)',p.name)[1]);assert n not in records,n;records[n]=r
assert set(records)==set(range(10600,10700))
roots=[]
for name in m['modules']+['R1Z.ProverCommitAudit54']:
 p=L/(name.replace('.','/')+'.lean');h=sha(p)
 matches=[r for r in records.values() if r.get('module')==name and r.get('source_sha256')==h and r.get('exit')==0]
 assert matches,('unverified live source',p)
 r=matches[-1]
 assert (E/'lean'/(r['attempt']+'.lean.txt')).read_bytes()==p.read_bytes()
 text=p.read_text()
 assert not re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*axiom\s|set_option\s+(?:maxRecDepth|maxHeartbeats)',text,re.M),p
 roots.append(dict(module=name,sha256=h,accepted_attempt=r['attempt']))
for r in m['roots']:assert sha(Path(r['path']))==r['sha256']
r=records[10699];assert r['exit']==0
out=r['out'];audited={};allowed={'propext','Classical.choice','Quot.sound'}
for name,ax in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",out):
 vals={x.strip() for x in ax.split(',') if x.strip()};assert vals<=allowed,(name,vals);audited[name]=sorted(vals)
for name in re.findall(r"'([^']+)' does not depend on any axioms",out):audited[name]=[]
expected=set(m['theorems'])|{'R1Z.ProverCommitDeployedFuel22.privacy_headline_deployed'}
assert set(audited)==expected,(len(audited),len(expected),expected-set(audited))
# Every theorem declaration in a new source is part of this audit.
found=set()
for name in m['modules']:
 p=L/(name.replace('.','/')+'.lean')
 for thm in re.findall(r'^theorem\s+(\S+)',p.read_text(),re.M):found.add(name+'.'+thm)
assert found==set(m['theorems']),(found-set(m['theorems']),set(m['theorems'])-found)
endpoint=L/'R1Z/ProverCommitDeployedFuel22.lean'
assert endpoint.read_bytes()==(E/'endpoint/before.lean.txt').read_bytes()==(E/'endpoint/after.lean.txt').read_bytes()
assert subprocess.check_output(['git','diff','4af6a0f6bf','--name-only','--','crates','programs'])==b''
pins=json.loads((E/'native-source-pins.json').read_text())
for name,pin in pins['pins'].items():assert sha(Path(pin['shipped']))==pin['sha256']
for name,h in pins['native_sources'].items():assert sha(E/'native'/name)==h
sim=Path(pins['simulator_source']['path']);assert sha(sim)==pins['simulator_source']['sha256']
assert all(span in sim.read_text() for span in pins['initial_projection']['shipped_spans'].values())
for p in E.rglob('*'):
 if p.is_file():assert p.suffix not in {'.olean','.o','.so','.a','.rlib','.llbc','.tar','.gz','.zip','.elf'},p
inventory=[]
for n,r in sorted(records.items()):
 inventory.append(dict(attempt='J'+str(n),module=r.get('module'),exit=r.get('exit'),compiler_invoked=r.get('compiler_invoked',None),reason=r.get('reason'),source_sha256=r.get('source_sha256')))
(E/'attempt-inventory.json').write_text(json.dumps(inventory,indent=2)+'\n')
result=dict(audit_attempt='J10699',source_revision=r.get('source_revision'),modules=roots,new_theorems=len(m['theorems']),axioms=audited,endpoint_sha256=sha(endpoint),shipped_files_changed=False,attempts_accounted=len(records),allocation_exhausted=True)
result['source_revision']=records[10699]['source_revision']
(E/'final-integrity.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(modules=len(roots),new_theorems=len(m['theorems']),axiom_reports=len(audited),attempts_accounted=len(records),shipped_files_changed=False,endpoint_sha256=sha(endpoint))))

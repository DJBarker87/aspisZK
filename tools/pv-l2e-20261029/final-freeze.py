"""Freeze focused replay and verify reused dependency objects read-only."""
from pathlib import Path
import subprocess,json,hashlib,re,shlex
E=Path('evidence/pv-l2e-20261029'); H='/home/dombarker/project-offloads/codex-pv-l2e-20261029'
sha=lambda b:hashlib.sha256(b).hexdigest()
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
receipts=sorted([json.load(open(p)) for p in E.glob('receipt-679*.json')],key=lambda x:x['attempt'])
latest={r['target']:r for r in receipts if r['accepted']}
for m,r in latest.items():
 b=Path('lean/'+m+'.lean').read_bytes()
 assert sha(b)==r['source_sha256']
 assert subprocess.check_output(['git','show',rev+':lean/'+m+'.lean'])==b
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',re.sub(r'/\-[\s\S]*?\-/|--[^\n]*','',b.decode()))
# Topological order; reused unchanged schema's object is verified rather than rebuilt.
pending=set(latest);order=[]
while pending:
 ready=sorted(m for m in pending if not (set(re.findall(r'^import (PV_L2E_\w+)',Path('lean/'+m+'.lean').read_text(),re.M)) & pending))
 assert ready,'cycle'
 order+=ready;pending-=set(ready)
remaining=67997-(67900+len(receipts))
assert remaining>=0
reuse=order[:len(order)-remaining] if remaining<len(order) else []
# Prefer reusing the unchanged original schema; all direct/transitive objects are checked below.
if len(reuse)==1:reuse=['PV_L2E_TraceMachine']
replay=[m for m in order if m not in reuse]
checks=json.load(open(E/'prepare-PV_L2E_TraceMachine.json'))['result']['checks']
# Add inherited L2D cohort checks from its h6 reuse records.
for p in E.glob('reuse-PV_L2D_*.json'):
 x=json.load(open(p))['result']
 checks.append(dict(module=x['module'],path=x['object']['path'],sha256=x['object']['sha256']))
for m,r in latest.items():checks.append(dict(module=m,path=H+'/objects/'+m+'.olean',sha256=r['object_sha256']))
code=r'''
import sys,json,pathlib,hashlib
x=json.load(sys.stdin);H=pathlib.Path(x['H']);env=json.load(open(H/'J.json'));roots=[pathlib.Path(p) for p in env['LEAN_PATH'].split(':')]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
results=[]
for c in x['checks']:
 m=c['module'];q=next(p/(m.replace('.','/')+'.olean') for p in roots if (p/(m.replace('.','/')+'.olean')).is_file())
 assert sha(q)==c['sha256'],('object changed',m,str(q))
 results.append(dict(module=m,path=str(q),sha256=c['sha256']))
for m,r in x['own'].items():
 assert sha(H/('sources/'+m+'.lean'))==r['source_sha256'],('source changed',m)
print(json.dumps(dict(toolchain=env['LEAN_GITHASH'],LEAN_PATH=env['LEAN_PATH'],objects=results,own_sources={m:r['source_sha256'] for m,r in x['own'].items()})))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(dict(H=H,checks=checks,own=latest)),text=True,capture_output=True)
(E/'final-cohort-check.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr,result=json.loads(r.stdout) if r.returncode==0 else r.stdout),indent=2)+'\n')
assert r.returncode==0,r.stderr
manifest=dict(source_revision=rev,focused_attempts=len(receipts),reused_own_objects=reuse,replay=[dict(attempt=67900+len(receipts)+i,module=m,sha256=latest[m]['source_sha256'])for i,m in enumerate(replay)],audits=[67997,67998,67999],scope='single incremental final focused manifest; no native endpoint or full deployed closure claim')
(E/'final-focused-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('PASS frozen',len(replay),'replay targets;',len(checks),'object hashes; reused own',reuse)

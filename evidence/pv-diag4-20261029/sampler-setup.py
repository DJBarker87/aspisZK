from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-diag4-20261029');P=D.parent/'codex-pv-diag3-20261029';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=json.loads((P/'project-resolution.json').read_text());pins=p['modules'];b=json.loads((D/'sampler-generation-chain.json').read_text());rows=json.loads((P/'accepted-cache-preflight.json').read_text())['rows'];a=set(b['sources'])
while True:
 c=a|{m for m,r in pins.items() if set(r['imports'])&a}
 if c==a:break
 a=c
# V2 step failed. Exclude its blocked endpoint; no stale object fallback.
a.discard('R1Z.PV_RunJoin_Deployed')
needed=set()
def visit(m):
 if m in needed:return
 needed.add(m)
 deps=pins[m]['imports'] if m in pins else rows[m].get('record_dependencies',{})
 for dep in deps:visit(dep)
visit('R1Z.PV_RunJoin_TrustItems')
assert 'R1Z.PrivacyR1HeadlineV2' not in needed
a.intersection_update(needed)
checks=[]
for m in needed:
 r=rows[m];assert sha(Path(r['path']))==r['sha256'],m
 if m in pins:assert r.get('source_sha256')==pins[m]['sha256'],m
 elif m in b['sources']:assert r.get('source_sha256')==b['sources'][m]['sha256'],m
 for dep,old in r.get('record_dependencies',{}).items():assert old['sha256']==rows[dep]['sha256'],(m,dep)
 checks.append(r)
for m in needed-a:
 if rows[m]['authority']=='h4 external':continue
 dst=D/'objects'/(m.replace('.','/')+'.olean');dst.parent.mkdir(parents=True,exist_ok=True)
 if not dst.exists():dst.symlink_to(rows[m]['path'])
for m in a:
 r=b['sources'].get(m) or pins[m];src=D/'sources'/(m.replace('.','/')+'.lean');src.parent.mkdir(parents=True,exist_ok=True)
 raw=(D/'source-inputs'/(m+'.lean.txt')).read_bytes();src.write_bytes(raw);assert sha(src)==r['sha256']
order=['ProverRwSampler.Types','ProverRwSampler.Funs']+[m for m in p['order'] if m in a]
(D/'sampler-rebuild-plan.json').write_text(json.dumps(dict(order=order,checked=len(checks),rows=checks,mismatches=[],blocked_endpoint='R1Z.PV_RunJoin_Deployed: failed fresh EJR V2'),indent=2)+'\n');print('checked',len(checks),'rebuild',len(order))

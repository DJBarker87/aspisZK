from pathlib import Path
import json,hashlib,lzma,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2h-20261029');G=D.with_name('codex-pv-rdb2g-20261029');F=D.with_name('codex-pv-rdb2f-20261029');O=D.with_name('codex-pv-rdb2e-20261029')/'lean-objects'
p=json.loads((D/'plan.json').read_text());env=json.loads((D/'env-J.json').read_text());old=json.loads((G/'preflight.json').read_text());f=json.loads(lzma.decompress((G/'fingerprint.json.xz').read_bytes()))
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
assert env==p['environment']==old['environment']==json.loads((O.parent/'env-J.json').read_text())
assert sha(Path(env['LEAN']))==old['lean_sha256']
assert sha(D.parent/'aspis-fs-generic-20261006/evidence/run2.py')==old['run2_sha256']
roots=list(map(Path,env['LEAN_PATH'].split(':')))
def obj(m):return next((root/(m.replace('.','/')+'.olean') for root in roots if(root/(m.replace('.','/')+'.olean')).exists()),None)
verified=[]
for r in p['objects']:
 m=r['module'];s=F/'lean-sources'/(m.replace('.','/')+'.lean');assert sha(s)==r['source']['sha256'],m
 if m in p['continuation_order']:assert not(O/(m.replace('.','/')+'.olean')).exists(),m
 else:
  prior=next(x for x in f['objects'] if x['module']==m);q=obj(m);assert str(q)==prior['path'] and sha(q)==prior['sha256']==r['object_sha256'],m
  for c in prior.get('companions',[]):assert sha(Path(c['path']))==c['sha256'],c
  for i in r['imports']:
   dep=obj(i['module']);assert dep and sha(dep)==i.get('sha256',i.get('object_sha256')),(m,i)
  verified.append(dict(module=m,path=str(q),sha256=sha(q),imports=r['imports'],companions=prior.get('companions',[])))
for x in p['external']:assert sha(obj(x['module']))==x['actual'],x['module']
coll=[]
for d in D.parent.glob('codex-pv-*'):
 if d!=D:coll.extend(str(q) for q in d.glob('lean-643[0-9][0-9]'))
sent=D.parent/'r1-privacy-build-integration-20261019/evidence/sent.txt'
if sent.exists():coll.extend(l for l in sent.read_text().splitlines() if re.search(r'\b643\d\d\b',l))
assert not coll,coll
j=dict(environment=env,exact_original_environment=True,effective_LEAN_PATH=str(O)+':'+env['LEAN_PATH'],lean_sha256=old['lean_sha256'],run2_sha256=old['run2_sha256'],source_count=len(p['objects']),external_count=len(p['external']),verified_cached=verified,remaining=p['continuation_order'],collisions=coll)
(D/'preflight.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(dict(verified_cached=len(verified),remaining=len(p['continuation_order']),sources=len(p['objects']),external=len(p['external']),collisions=coll)))

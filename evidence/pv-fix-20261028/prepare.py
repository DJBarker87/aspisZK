from pathlib import Path
import json,hashlib,os,re
D=Path('/home/dombarker/project-offloads/codex-pv-fix-20261028');P=D.parent;R=P/'codex-pv-rdcd-20261028';C=P/'codex-pv-rdeac-20261028'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(n,r):(D/n).write_text(json.dumps(r,indent=2)+'\n')
def roots(env,front):return [front]+[Path(x) for x in env['LEAN_PATH'].split(':')]
def obj(m,rs):return next((r/(m.replace('.','/')+'.olean') for r in rs if (r/(m.replace('.','/')+'.olean')).is_file()),None)
# The scan includes shared sent.txt and every other privacy job's receipt/output names.
hits=[];pat=re.compile(r'(?:^|[-_])620\d\d(?:[-_.]|$)')
for job in P.glob('codex-pv-*'):
 if job==D:continue
 for root,dirs,files in os.walk(job):
  dirs[:]=[x for x in dirs if x not in ['target','client-target','objects','lean-objects','actual-objects','sources','lean-sources','actual-sources','source','src','node_modules','.git','.lake','native-source','repo']]
  for n in files:
   if pat.search(n):hits.append(str(Path(root)/n))
sents=[]
for p in [P/'r1-privacy-build-integration-20261019/evidence/sent.txt',P/'codex-pv-envfix-20261026/evidence/sent.txt',P/'codex-pv-replay-20261027/evidence/sent.txt',P/'aspis-fs-generic-20261006/evidence/sent.txt']:
 if not p.exists():continue
 lines=[l for l in p.read_text(errors='replace').splitlines() if any(x.isdigit() and 62000<=int(x)<=62099 for x in l.split())]
 if lines:sents.append(dict(path=str(p),matches=lines))
save('id-scan.json',dict(range=[62000,62099],receipt_hits=hits,sent_hits=sents));assert not hits and not sents
external=json.loads((R/'external-object-manifest.json').read_text());save('external-authority.json',dict(path=str(R/'external-object-manifest.json'),sha256=sha(R/'external-object-manifest.json')))
affected={r['module'] for r in json.loads((D/'affected-order.json').read_text())};pre={}
for cohort,base,front in [('rdcd',R,R/'lean-objects'),('rdeac',C,C/'objects')]:
 env=json.loads((base/'env-J.json').read_text());rs=roots(env,front);checks=[]
 for r in external:
  m=r['module'];q=obj(m,rs);assert q and sha(q)==r['object_sha256'],(cohort,m,q)
  checks.append(dict(module=m,path=str(q),object_sha256=sha(q)))
 own=D/cohort/'objects';own.mkdir(parents=True,exist_ok=True)
 if cohort=='rdcd':
  graph=json.loads((R/'resume-final-fingerprint.json').read_text())['modules'];records=[]
  for m,r in graph.items():
   src=R/'lean-sources'/(m+'.lean');q=obj(m,rs);assert sha(src)==r['sha256'],m
   if q:assert sha(q)==r['object_sha256'],m
   deps=[]
   for dep,j in r['resolved_imports'].items():
    p=obj(dep,rs);assert not p or sha(p)==j['object_sha256'],(m,dep)
    deps.append(dict(module=dep,path=str(p) if p else None,object_sha256=j['object_sha256']))
   records.append(dict(module=m,source=str(src),source_sha256=sha(src),source_blob=r['blob'],object=str(q) if q else None,object_sha256=r['object_sha256'],imports=deps))
  for r in records:
   m=r['module'];p=own/(m+'.olean');p.parent.mkdir(parents=True,exist_ok=True)
   if m not in affected and r['object']:p.symlink_to(r['object'])
  # Exclude old void objects from every path, not merely shadow them.
  env['LEAN_PATH']=':'.join(x for x in env['LEAN_PATH'].split(':') if x!=str(front))
 else:
  f=json.loads((C/'final-preflight.json').read_text());records=f['projects'];pins={r['module']:r for r in json.loads((C/'final-source-pins.json').read_text())}
  for r in records:
   m=r['module'];assert sha(r['source'])==r['source_sha256'],m
   q=obj(m,rs);expected=r['object_sha256']
   if expected is None:
    assert m=='R1Z.PV_RDEAC_Statements';expected=json.loads((C/'receipt-61197.json').read_text())['object_sha256']
   assert q and sha(q)==expected,(m,q)
   r['object']=str(q);r['object_sha256']=expected
   for j in r['imports']:
    p=obj(j['module'],rs);assert p and sha(p)==j['object_sha256'],(m,j['module'])
  m='R1Z.PV_RDEAC_Axioms';src=C/'sources'/(m.replace('.','/')+'.lean');q=obj(m,rs);rec=json.loads((C/'receipt-61198.json').read_text());assert sha(src)==rec['source_sha256'] and sha(q)==rec['object_sha256']
  records.append(dict(module=m,source=str(src),source_sha256=sha(src),source_blob=pins[m]['blob'],object=str(q),object_sha256=sha(q),imports=[dict(module='R1Z.PV_RDEAC_Statements',path=str(obj('R1Z.PV_RDEAC_Statements',rs)),object_sha256=sha(obj('R1Z.PV_RDEAC_Statements',rs)))]))
  for r in records:
   p=own/(r['module'].replace('.','/')+'.olean');p.parent.mkdir(parents=True,exist_ok=True);p.symlink_to(r['object'])
 # Record original toolchain and LEAN_PATH in full; only private overlay is changed.
 save(cohort+'-env.json',env);pre[cohort]=dict(original_environment=json.loads((base/'env-J.json').read_text()),environment=env,external=checks,projects=records,ok=True)
save('preflight.json',pre);print('verified external manifests, source pins and all recorded import edges; prepared private read-only caches')

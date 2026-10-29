from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-fix-20261028');P=D.parent;sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(n,r):(D/n).write_text(json.dumps(r,indent=2)+'\n')
R=P/'codex-pv-rdcd-20261028';C=P/'codex-pv-rdeac-20261028';external=json.loads((R/'external-object-manifest.json').read_text());pre={};X=D/'external-objects';X.mkdir(exist_ok=True)
for cohort,B,front in [('rdcd',R,R/'lean-objects'),('rdeac',C,C/'objects')]:
 env=json.loads((B/'env-J.json').read_text());rs=[front]+[Path(x) for x in env['LEAN_PATH'].split(':')]
 def obj(m):return next((r/(m.replace('.','/')+'.olean') for r in rs if (r/(m.replace('.','/')+'.olean')).is_file()),None)
 checks=[]
 for r in external:
  m=r['module'];q=obj(m);assert q and sha(q)==r['object_sha256'],(cohort,m)
  p=X/(m.replace('.','/')+'.olean');p.parent.mkdir(parents=True,exist_ok=True)
  if not p.exists():p.symlink_to(q)
  assert sha(p)==r['object_sha256'];checks.append(dict(module=m,path=str(q),object_sha256=sha(q)))
 O=D/cohort/'objects';O.mkdir(parents=True,exist_ok=True);records=[];mismatches=[];missing=[]
 if cohort=='rdcd':
  graph=json.loads((R/'resume-final-fingerprint.json').read_text())['modules']
  for m,r in graph.items():
   src=R/'lean-sources'/(m+'.lean');assert sha(src)==r['sha256'],m;q=obj(m)
   if not q:missing.append(m)
   elif sha(q)!=r['object_sha256']:mismatches.append(dict(module=m,path=str(q),observed=sha(q),expected=r['object_sha256']));q=None
   records.append(dict(module=m,source=str(src),source_sha256=sha(src),source_blob=r['blob'],object=str(q) if q else None,object_sha256=r['object_sha256'],imports=[dict(module=n,object_sha256=j['object_sha256']) for n,j in r['resolved_imports'].items()]))
  # Only reuse an object whose entire recorded closure is present and coherent.
  rec={r['module']:r for r in records};ext={r['module'] for r in external};safe={}
  def valid(m):
   if m in ext:return True
   if m in safe:return safe[m]
   r=rec[m];safe[m]=False
   safe[m]=bool(r['object']) and all(valid(j['module']) and (j['module'] in ext or rec[j['module']]['object_sha256']==j['object_sha256']) for j in r['imports']);return safe[m]
  affected={r['module'] for r in json.loads((D/'affected-order.json').read_text())}
  for r in records:
   m=r['module'];p=O/(m+'.olean');p.parent.mkdir(parents=True,exist_ok=True)
   if valid(m) and m not in affected and not p.exists():p.symlink_to(r['object'])
 else:
  records=json.loads((C/'final-preflight.json').read_text())['projects'];pins={r['module']:r for r in json.loads((C/'final-source-pins.json').read_text())}
  for r in records:
   m=r['module'];assert sha(r['source'])==r['source_sha256'];q=obj(m);expected=r['object_sha256']
   if expected is None:assert m=='R1Z.PV_RDEAC_Statements';expected=json.loads((C/'receipt-61197.json').read_text())['object_sha256']
   assert q and sha(q)==expected,(m,q);r['object']=str(q);r['object_sha256']=expected
   for j in r['imports']:assert sha(obj(j['module']))==j['object_sha256'],(m,j['module'])
  m='R1Z.PV_RDEAC_Axioms';src=C/'sources'/(m.replace('.','/')+'.lean');q=obj(m);r=json.loads((C/'receipt-61198.json').read_text());assert sha(src)==r['source_sha256'] and sha(q)==r['object_sha256']
  records.append(dict(module=m,source=str(src),source_sha256=sha(src),source_blob=pins[m]['blob'],object=str(q),object_sha256=sha(q),imports=[dict(module='R1Z.PV_RDEAC_Statements',object_sha256=sha(obj('R1Z.PV_RDEAC_Statements')))]))
  for r in records:
   p=O/(r['module'].replace('.','/')+'.olean');p.parent.mkdir(parents=True,exist_ok=True)
   if not p.exists():p.symlink_to(r['object'])
 old=env.copy();env['LEAN_PATH']=str(X);save(cohort+'-env.json',env);pre[cohort]=dict(original_environment=old,environment=env,external=checks,projects=records,missing_objects=missing,mismatched_objects=mismatches,ok=True,policy='External-only LEAN_PATH plus private objects; unavailable/mismatched project objects cannot fall through to historical cohorts.')
save('preflight.json',pre);print('Prepared both isolated cohorts; no stale project fallback. RDCD missing',len(pre['rdcd']['missing_objects']),'mismatched',len(pre['rdcd']['mismatched_objects']))

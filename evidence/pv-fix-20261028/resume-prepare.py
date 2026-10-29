from pathlib import Path
import json,hashlib,os,re
D=Path('/home/dombarker/project-offloads/codex-pv-fix-20261028');P=D.parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(n,v):(D/n).write_text(json.dumps(v,indent=2)+'\n')
hits=[];pat=re.compile(r'(?:^|[-_])621\d\d(?:[-_.]|$)')
for job in P.glob('codex-pv-*'):
 for root,dirs,files in os.walk(job):
  dirs[:]=[x for x in dirs if x not in ['target','client-target','objects','lean-objects','actual-objects','sources','lean-sources','actual-sources','source','src','node_modules','.git','.lake','native-source','repo','external-objects']]
  for n in files:
   if pat.search(n):hits.append(str(Path(root)/n))
sents=[]
for p in P.glob('*/evidence/sent.txt'):
 for l in p.read_text(errors='replace').splitlines():
  if any(x.isdigit() and 62100<=int(x)<=62199 for x in l.split()):sents.append(dict(path=str(p),line=l))
save('resume-id-scan.json',dict(range=[62100,62199],receipt_hits=hits,sent_hits=sents));assert not hits and not sents
pre=json.loads((D/'preflight.json').read_text())['rdcd'];ext={r['module'].replace('.','/'):r for r in pre['external']}
checked=[]
for n,r in ext.items():
 p=D/'external-objects'/(n+'.olean');assert sha(p)==r['object_sha256'],n
 checked.append(dict(module=n,path=str(p),sha256=sha(p)))
save('resume-external-check.json',checked)
env=json.loads((D/'rdcd-env.json').read_text());assert env==json.loads((D/'env-62014.json').read_text());save('resume-env.json',env)
records={r['module']:r for r in pre['projects']};fresh={r['module']:r for p in sorted(D.glob('receipt-620*.json')) if (r:=json.loads(p.read_text())).get('exit')==0 and r['cohort']=='rdcd'}
valid={};verified={};plan=[]
def visit(n):
 if n in ext:return ext[n]['object_sha256']
 if n in valid:return valid[n]
 r=records[n];s=Path(r['source']);assert sha(s)==r['source_sha256'],n
 deps={j['module']:visit(j['module']) for j in r['imports']}
 p=D/'rdcd/objects'/(n+'.olean');fr=fresh.get(n)
 expect=fr['object_sha256'] if fr else r['object_sha256']
 expected_deps={j['module']:j['object_sha256'] for j in r['imports']}
 if fr:
  for c,v in fr['dependencies'].items():
   if c in expected_deps:expected_deps[c]=v['object_sha256']
 ok=p.is_file() and sha(p)==expect and all(v is not None and v==expected_deps[c] for c,v in deps.items())
 if ok:
  verified[n]=dict(source_sha256=sha(s),source_blob=r['source_blob'],object_sha256=expect,imports=deps,receipt=fr['attempt'] if fr else 'inherited coherent cache',object_path=str(p))
  valid[n]=expect
 else:
  valid[n]=None;plan.append(n)
 return valid[n]
visit('R1Z/PV_RDCD_FinalManifest')
save('resume-cache-check.json',verified);save('resume-plan.json',plan)
print(json.dumps(dict(verified_projects=len(verified),external=len(checked),rebuild_count=len(plan),plan=plan),indent=2))

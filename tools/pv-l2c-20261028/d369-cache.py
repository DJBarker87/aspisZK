"""Read-only pinned cache selection; copy only new verified Stream B objects."""
from pathlib import Path
import json,subprocess,shlex,hashlib,gzip
R=Path(__file__).resolve().parents[2]; E=R/'evidence/pv-l2c-20261028/resume-d369'
r=json.loads((E/'focused-resolution.json').read_text());res=r['resolved']; assert not r['unpinned']
old=json.load(open(R/'evidence/pv-l2c-20261028/resume-d355/final-closure-check.json'))['objects']
prior=json.load(open(R/'evidence/pv-l2c-20261028/resume-d355/focused-resolution.json'))['resolved']
checks={x['module']:x for x in json.load(open(R/'evidence/pv-runjoin31-20261028/focused-project-cache-check.json'))}
receipts={}
for p in sorted((R/'evidence').glob('pv-runjoin*/receipt-*.json')):
 try:x=json.load(open(p))
 except:continue
 if isinstance(x,dict) and x.get('exit')==0 and 'sorryAx' not in str(x.get('axioms')):
  m=x.get('target',x.get('module','')).replace('/','.')
  receipts[(m,x.get('source_sha256'))]=(x,str(p.relative_to(R)))
rows={};missing=[]
for m,x in res.items():
 if 'imports' not in x:rows[m]=dict(path=x['path'],sha256=x['object_sha256'],external=True);continue
 if m in old and prior[m].get('sha256')==x['sha256']:
  rows[m]=dict(path=old[m]['path'],sha256=old[m]['sha256'],external=False,source=x,authority='D355 complete closure audit');continue
 c=checks.get(m);rc=receipts.get((m,x['sha256']))
 if c and c.get('expected_sha256')==x['sha256'] and (c.get('source_match') or c.get('retained_own_cache_source_match')) and rc:
  a,p=rc; rows[m]=dict(path=c['object_path'],sha256=c['object_sha256'],external=False,source=x,receipt=p,dependencies=a['dependencies'],authority='h6 source match and accepted source receipt')
 elif c and c.get('source_match') and c.get('expected_sha256')==x['sha256']:
  rows[m]=dict(path=c['object_path'],sha256=c['object_sha256'],external=False,source=x,source_check=c,authority='h6 scoped runjoin31 final source check')
 else:missing.append(m)
print('Unresolved cache',missing)
(E/'cache-plan.json').write_text(json.dumps(dict(objects=rows,missing=missing),indent=2)+'\n')
code=r'''import json,sys,pathlib,hashlib
z=json.load(sys.stdin);rows=z['objects'];H=pathlib.Path('/home/dombarker/project-offloads/codex-pv-l2c-20261028/lean');e=json.load(open(H/'J.json'));other=json.load(open('/home/dombarker/project-offloads/codex-pv-runjoin-20261026/runjoin24-lean/J.json'));assert {k:v for k,v in e.items() if k!='LEAN_PATH'}=={k:v for k,v in other.items() if k!='LEAN_PATH'}
fail=[]
for m,x in rows.items():
 p=pathlib.Path(x['path']);assert p.is_file(),m
 assert hashlib.sha256(p.read_bytes()).hexdigest()==x['sha256'],m
 for d,v in x.get('dependencies',{}).items():
  if d not in rows or rows[d]['sha256']!=v['sha256']:fail.append([m,d,v,rows.get(d)])
assert not fail,fail
otherroots=[pathlib.Path(p) for p in other['LEAN_PATH'].split(':')]
for m,x in rows.items():
 if x['external'] or x['authority']=='D355 complete closure audit':continue
 actualdeps={}
 for d in x['source']['imports']:
  q=next(root/(d.replace('.','/')+'.olean') for root in otherroots if (root/(d.replace('.','/')+'.olean')).is_file())
  h=hashlib.sha256(q.read_bytes()).hexdigest();assert h==rows[d]['sha256'],(m,d,h,rows[d]['sha256']);actualdeps[d]=h
 x['complete_direct_fingerprint']=actualdeps
# h6 dependency equality is checked before adding any private-view link.
for m,x in rows.items():
 if x['external'] or x['authority']=='D355 complete closure audit':continue
 p=pathlib.Path(x['path'])
 for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']:
  q=pathlib.Path(str(p)[:-6]+suffix)
  if not q.is_file():continue
  dest=H/'objects'/(m.replace('.','/')+suffix);dest.parent.mkdir(parents=True,exist_ok=True)
  if dest.exists() or dest.is_symlink():assert dest.is_file() and hashlib.sha256(dest.read_bytes()).digest()==hashlib.sha256(q.read_bytes()).digest(),str(dest)
  else:dest.symlink_to(q.resolve())
print(json.dumps(dict(toolchain_match=True,direct_and_transitive_match=True,objects=rows)))
'''
p=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(dict(objects=rows)),capture_output=True,text=True)
(E/'cache-check.log').write_text(p.stdout+p.stderr);assert p.returncode==0,p.stderr
(E/'cache-check.json').write_text(p.stdout)
print('Verified',len(rows),'objects')

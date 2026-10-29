"""Resolve one row's actual proof cone; no compiler or shared-source writes."""
from pathlib import Path
import subprocess,json,hashlib,re,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2d-20261028'
def git(key):return subprocess.check_output(['git','show',key],cwd=R)
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
inv=json.loads(git('research:evidence/envj-rebuild-20261026/EJR_final-inventory.json'))
replay=json.loads(git('research:evidence/pv-replay-20261027/replay-plan.json'))['nodes']
ejr={}
for r in inv['selected']:
 if not r.get('resolution'):continue
 m=r['module'].replace('/','.')
 key=r['module'].replace('.','/')
 if m not in ejr or (key in replay and r['sha256']==replay[key]['source_sha256']):ejr[m]=r
ext={r['module'].replace('/','.'):r for r in json.loads(git('research:evidence/pv-replay-20261027/receipts/external-object-manifest.json'))}
freeze=json.loads(git('research:docs/research/100bit-spend-path-20261013/evidence/prover-commit47-20261022/final-source-freeze.json'))
fz={r['module']:r for r in freeze['sources']}
ejs={r['module'].replace('/','.'):r for r in json.loads(git('research:evidence/envj-rebuild2-20261026/EJS_missing-payload.json'))['rows']}
previous={}
paths=subprocess.check_output(['git','ls-files','*.lean','*.lean.txt','*.lean.host.txt'],cwd=R,text=True).splitlines()
done={};missing={};order=[]
def uncomment(s):
 out=[];i=0;depth=0
 while i<len(s):
  if s[i:i+2]=='/-':depth+=1;i+=2
  elif depth and s[i:i+2]=='-/':depth-=1;i+=2
  elif depth:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif s[i:i+2]=='--':
   end=s.find('\n',i);i=len(s) if end<0 else end
  else:out.append(s[i]);i+=1
 return ''.join(out)
def visit(m):
 if m in done or m in missing or m in ext:return
 assert not any(x.startswith('XR') for x in m.split('.')),m
 if m in ejr:
  row=ejr[m];r=row['resolution'];p=r['path'];blob=r['blob'];b=git(blob);expected=row['sha256'];authority='EJR'
 elif m in fz:
  r=fz[m];p=r['path'];key=freeze['revision']+':'+p;b=git(key);expected=r['sha256'];blob=subprocess.check_output(['git','rev-parse',key],cwd=R,text=True).strip();authority='freeze47'
 elif m in ejs:
  r=ejs[m];p=r['path'];blob=r['blob'];b=git(blob);expected=r['source_sha256'];authority='EJS SHA-pinned rebuild record'
 else:
  suffix=m.replace('.','/')+'.lean'
  ps=[p for p in paths if p.endswith('/lean/'+suffix)]
  if not ps and m in previous and previous[m]['path'] in paths:
   # This is a source locator only: own HEAD is checked, never an object pin.
   ps=[previous[m]['path']]
  if not ps:ps=[p for p in paths if p.endswith('/'+suffix) or p.endswith('/'+m+'.lean.txt')]
  hashes={p:hashlib.sha256(git(head+':'+p)).hexdigest() for p in ps}
  if len(set(hashes.values()))!=1:missing[m]=hashes;return
  p=ps[0];b=git(head+':'+p);expected=hashes[p];blob=subprocess.check_output(['git','rev-parse',head+':'+p],cwd=R,text=True).strip();authority='h5 own HEAD'
 assert hashlib.sha256(b).hexdigest()==expected,m
 imports=re.findall(r'^(?:public )?import\s+(\S+)',uncomment(b.decode()),re.M)
 conflicts=[]
 for q in paths:
  if q.endswith('/lean/'+m.replace('.','/')+'.lean'):
   h=hashlib.sha256(git(head+':'+q)).hexdigest()
   if h!=expected:conflicts.append(dict(path=q,sha256=h))
 done[m]=dict(path=p,blob=blob,sha256=expected,authority=authority,imports=imports,tracked_conflicts=conflicts)
 for x in imports:visit(x)
 order.append(m)
label,*roots=sys.argv[1:]
for m in roots:visit(m)
(E/(label+'-resolution.json')).write_text(json.dumps(dict(head=head,roots=roots,modules=done,order=order,missing=missing,external=ext),indent=2)+'\n')
print(json.dumps(dict(project_modules=len(done),unresolved=missing)))

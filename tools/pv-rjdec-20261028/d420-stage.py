"""Resolve unchanged dependencies; retain EJR precedence and exact snapshot pins."""
from pathlib import Path
import subprocess,json,re,hashlib,shlex,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rjdec-20261028'
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
read=lambda p:subprocess.check_output(['git','show',rev+':'+p])
sha=lambda b:hashlib.sha256(b).hexdigest()
plan=json.loads((E/'build-plan.json').read_text())
external={v['module'].replace('/','.') for v in json.loads((E/'external-authority.json').read_text())}
ejr={v['module'].replace('/','.'):v for v in json.loads(read('evidence/envj-rebuild-20261026/EJR_final-inventory.json'))['selected']}
old=json.loads(read('evidence/pv-2tnv-20261028/resume/source-closure.json'))['modules']
files=set(subprocess.check_output(['git','ls-files'],text=True).splitlines());data={};order=[]
def visit(m):
 if m in plan['modules'] or m in external or m in data:return
 if m in ejr:
  ep=ejr[m];path=ep['resolution']['path'];b=read(path);assert sha(b)==ep['sha256'],(m,'EJR HEAD mismatch')
  authority='EJR_final-inventory.json';extra={}
 elif m in old:
  historical=old[m]; snapshot='evidence/pv-2tnv-20261028/resume/'+m+'.lean.txt'
  path=historical['path']
  if path not in files or sha(read(path)) != historical['sha256']: path=snapshot
  assert path in files,('COHORT GAP no exact tracked snapshot',m)
  b=read(path);assert sha(b)==historical['sha256'],(m,'historical snapshot mismatch')
  assert b==subprocess.check_output(['git','show',historical['revision']+':'+historical['path']]),m
  authority='h5 own git-tracked HEAD exact retained predecessor source';extra={'snapshot_authority':'evidence/pv-2tnv-20261028/resume/source-closure.json','historical_pin':historical}
 else:
  candidates=[m.replace('.','/')+'.lean','lean/'+m.replace('.','/')+'.lean','docs/research/v8-r0-zk-20261009/lean/'+m.replace('.','/')+'.lean','docs/research/100bit-spend-path-20261013/lean/'+m.replace('.','/')+'.lean']
  paths=[p for p in candidates if p in files]
  if not paths: paths=[p for p in files if p.endswith('/'+m.replace('.','/')+'.lean')]
  if paths:
   assert len(paths)==1,(m,paths);path=paths[0];b=read(path);extra={};authority='h5 own git-tracked HEAD'
  else:
   path='evidence/pv-2tnv-20261028/resume/'+m+'.lean.txt'
   assert m in old and path in files,('COHORT GAP',m)
   b=read(path);assert sha(b)==old[m]['sha256'],(m,'historical snapshot mismatch')
   assert b==subprocess.check_output(['git','show',old[m]['revision']+':'+old[m]['path']]),m
   authority='h5 own git-tracked HEAD exact retained source snapshot';extra={'snapshot_authority':'evidence/pv-2tnv-20261028/resume/source-closure.json','historical_pin':old[m]}
 imports=re.findall(r'^(?:public )?import\s+(\S+)',b.decode(),re.M)
 pin=dict(authority=authority,path=path,revision=rev,git_blob=subprocess.check_output(['git','rev-parse',rev+':'+path],text=True).strip(),sha256=sha(b),imports=imports,tracked_conflicts=[],**extra)
 data[m]=(pin,b.decode())
 for d in imports:visit(d)
 order.append(m)
for m in sys.argv[1:]:visit(m)
code=r'''import pathlib,json,sys,hashlib
x=json.load(sys.stdin);p=pathlib.Path(x['workspace']);plan=json.load(open(p/'build-plan.json'))
for m in x['order']:
 pin,s=x['data'][m];q=p/'sources'/(m.replace('.','/')+'.lean');o=p/'objects'/(m.replace('.','/')+'.olean');assert not o.exists(),m
 if q.exists():assert q.read_text()==s,('staged source mismatch',m)
 q.parent.mkdir(parents=True,exist_ok=True);q.write_text(s);assert hashlib.sha256(q.read_bytes()).hexdigest()==pin['sha256'];plan['modules'][m]=pin
(p/'build-plan.json').write_text(json.dumps(plan));print(json.dumps({'staged':len(x['order'])}))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(dict(workspace=plan['workspace'],order=order,data=data)),text=True,capture_output=True);assert r.returncode==0,r.stderr
for m,(pin,s) in data.items():plan['modules'][m]=pin
(E/'build-plan.json').write_text(json.dumps(plan,indent=2)+'\n')
(E/'d420-staged.json').write_text(json.dumps(dict(revision=rev,targets=sys.argv[1:],order=order,pins={m:v[0] for m,v in data.items()}),indent=2)+'\n')
print(r.stdout);print('topological order:',order)

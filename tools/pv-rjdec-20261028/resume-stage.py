"""Resolve additional unchanged sources and stage only private inputs."""
from pathlib import Path
import subprocess,json,re,hashlib,shlex,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rjdec-20261028';plan=json.loads((E/'build-plan.json').read_text());rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
read=lambda p:subprocess.check_output(['git','show',rev+':'+p])
external={v['module'].replace('/','.') for v in json.loads((E/'external-authority.json').read_text())}
files=subprocess.check_output(['git','ls-files','*.lean'],text=True).splitlines();order=[];data={}
def visit(m):
 if m in plan['modules'] or m in external or m in data:return
 matches=[f for f in files if f.endswith('/'+m.replace('.','/')+'.lean') or f==m.replace('.','/')+'.lean']
 assert len(matches)==1,(m,matches)
 path=matches[0];b=read(path);imports=re.findall(r'^(?:public )?import\s+(\S+)',b.decode(),re.M)
 pin=dict(authority='h5 own git-tracked HEAD',path=path,git_blob=subprocess.check_output(['git','rev-parse',rev+':'+path],text=True).strip(),sha256=hashlib.sha256(b).hexdigest(),imports=imports,revision=rev,tracked_conflicts=[])
 # New RDCD/RJDec prefixes are not historic EJR/freeze modules.
 assert m.startswith(('R1Z.PV_RDCD_','R1Z.PV_RJDec_'))
 data[m]=(pin,b.decode())
 for d in imports:visit(d)
 order.append(m)
for m in sys.argv[1:]:visit(m)
code=r'''import pathlib,json,sys,hashlib
x=json.load(sys.stdin);p=pathlib.Path(x['workspace']);plan=json.load(open(p/'build-plan.json'))
for m in x['order']:
 pin,s=x['data'][m];q=p/'sources'/(m.replace('.','/')+'.lean');o=p/'objects'/(m.replace('.','/')+'.olean');assert not o.exists(),m
 q.parent.mkdir(parents=True,exist_ok=True);q.write_text(s);assert hashlib.sha256(q.read_bytes()).hexdigest()==pin['sha256'];plan['modules'][m]=pin
(p/'build-plan.json').write_text(json.dumps(plan));print(json.dumps(x['order']))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(dict(workspace=plan['workspace'],data=data,order=order)),text=True,capture_output=True);assert r.returncode==0,r.stderr
for m,(pin,_) in data.items():plan['modules'][m]=pin
(E/'build-plan.json').write_text(json.dumps(plan,indent=2)+'\n');(E/'resume-staged.json').write_text(json.dumps(dict(order=order,pins={m:p for m,(p,_) in data.items()}),indent=2)+'\n');print(r.stdout)

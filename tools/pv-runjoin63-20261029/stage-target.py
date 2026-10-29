"""Stage one committed new PV module for a focused attempt in the fresh workspace."""
from pathlib import Path
import sys,json,subprocess,hashlib,re,shlex
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin63-20261029';m=sys.argv[1];assert m.startswith(('R1Z.PV_','PV_','JFx_','JHb_','JHg_'))
fixture=json.loads((E/'fixture-pins.json').read_text())['modules']
s=R/fixture[m]['path'] if m in fixture else R/'docs/research/v8-r0-zk-20261009/lean'/(m.replace('.','/')+'.lean');path=str(s.relative_to(R));rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();b=subprocess.check_output(['git','show',rev+':'+path]);assert b==s.read_bytes(),'commit exact source first'
plan=json.loads((E/'build-plan.json').read_text());external={v['module'].replace('/','.') for v in json.loads((E/'external-authority.json').read_text())};imports=re.findall(r'^(?:public )?import\s+(\S+)',b.decode(),re.M)
assert all(d in plan['modules'] or d in external for d in imports),[d for d in imports if d not in plan['modules'] and d not in external]
pin=dict(authority='h5 own git-tracked HEAD',path=path,git_blob=subprocess.check_output(['git','rev-parse',rev+':'+path],text=True).strip(),sha256=hashlib.sha256(b).hexdigest(),imports=imports,tracked_conflicts=[],revision=rev)
code=r'''import json,pathlib,sys,hashlib
x=json.load(sys.stdin);p=pathlib.Path(x['workspace']);m=x['module'];q=p/'sources'/(m.replace('.','/')+'.lean');o=p/'objects'/(m.replace('.','/')+'.olean');assert not o.exists(),'accepted object must be retained'
if q.is_file():
 old=q.read_bytes();archive=p/'source-history'/hashlib.sha256(old).hexdigest();archive.parent.mkdir(exist_ok=True);archive.write_bytes(old)
q.parent.mkdir(parents=True,exist_ok=True);q.write_text(x['source']);assert hashlib.sha256(q.read_bytes()).hexdigest()==x['pin']['sha256']
plan=json.load(open(p/'build-plan.json'));plan['modules'][m]=x['pin'];(p/'build-plan.json').write_text(json.dumps(plan));print('staged',m,x['pin']['sha256'])
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(dict(workspace=plan['workspace'],module=m,source=b.decode(),pin=pin)),text=True,capture_output=True)
(E/(m.split('.')[-1]+'-staging.json')).write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr,pin=pin),indent=2)+'\n');assert r.returncode==0,r.stderr
plan['modules'][m]=pin;(E/'build-plan.json').write_text(json.dumps(plan,indent=2)+'\n');print(r.stdout)

from pathlib import Path
import json,re,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-dlib-20261028';D='/home/dombarker/project-offloads/codex-pv-dlib-20261028';pins=json.loads((E/'dependency-source-pins.json').read_text());external={j['module']:j for j in json.loads((E/'external-object-manifest.json').read_text())};seen={};passed={}
for p in E.glob('lean-*/receipt.json'):
 j=json.loads(p.read_text())
 if j.get('exit')==0 and j.get('module'):passed[j['module']]=j
roots=json.loads((E/'resume-audit-roots.json').read_text())['imports']
for m in ['R1Z/PV_DL_ResumeAudit','R1Z/PV_DL_ResumeReplay','R1Z/PV_DL_ResumeAuditReplay']:
 if m in passed:roots.append(m)
def visit(m):
 if m in seen:return
 assert 'XR' not in m,m
 if m in external:seen[m]={'external':True,'object_sha256':external[m]['object_sha256']};return
 p=R/pins[m]['path'] if m in pins else R/'docs/research/v8-r0-zk-20261009/lean'/(m+'.lean')
 s=p.read_bytes();sha=hashlib.sha256(s).hexdigest();assert passed[m]['source_sha256']==sha,(m,'not green at current source')
 deps=[x.replace('.','/') for x in re.findall(r'^import (\S+)',s.decode(),re.M)]
 seen[m]=dict(source_path=str(p.relative_to(R)),source_sha256=sha,blob=subprocess.check_output(['git','rev-parse','HEAD:'+str(p.relative_to(R))],text=True).strip(),imports=deps)
 for d in deps:visit(d)
for m in roots:visit(m)
project={m:j for m,j in seen.items() if not j.get('external')}
code='''from pathlib import Path
import json,hashlib
b=Path(DIR);out={}
for m,j in PROJECT.items():
 s=b/'lean-sources'/(m+'.lean');p=b/'lean-objects'/(m+'.olean')
 h=hashlib.sha256(s.read_bytes()).hexdigest();assert h==j['source_sha256'],m
 out[m]=dict(source_sha256=h,object_path=str(p),object_sha256=hashlib.sha256(p.read_bytes()).hexdigest())
env=json.loads((b/'env-J.json').read_text());roots=[Path(x) for x in env['LEAN_PATH'].split(':')]
external_bad=[]
for m,j in EXTERNAL.items():
 p=next((r/(m+'.olean') for r in roots if (r/(m+'.olean')).exists()),None)
 assert p is not None,('missing external',m)
 if hashlib.sha256(p.read_bytes()).hexdigest()!=j['object_sha256']:external_bad.append(m)
assert not external_bad,external_bad
for m,j in RECEIPTS.items():
 for dep,expected in j.get('imports',{}).items():
  p=next((r/(dep.replace('.','/')+'.olean') for r in roots if (r/(dep.replace('.','/')+'.olean')).exists()),None)
  assert p is not None and hashlib.sha256(p.read_bytes()).hexdigest()==expected['sha256'],('changed loaded dependency',m,dep)

print(json.dumps(dict(project=out,environment=json.loads((b/'env-J.json').read_text())),indent=2))
'''.replace('DIR',repr(D)).replace('PROJECT',repr(project)).replace('EXTERNAL',repr(external)).replace('RECEIPTS',repr({m:passed[m] for m in project}))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
j=json.loads(r.stdout);j.update(roots=roots,source_closure=seen,revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),external_authority='external-object-manifest.json; all5673 precompile verified',other_job_project_objects_reused=False)
(E/'resume-final-closure-fingerprint.json').write_text(json.dumps(j,indent=2)+'\n');print(len(project),'project sources/objects matched')

from pathlib import Path
import json,subprocess,shlex,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2d-20261028';host='dombarker@100.108.41.90';H='/home/dombarker/project-offloads/codex-pv-l2d-20261028'
x=json.loads((E/'external-authority.json').read_text())
code='''import sys,json,pathlib,hashlib
x=json.load(sys.stdin);bad=[]
for r in x:
 p=pathlib.Path(r['path']);h=hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None
 if h!=r['object_sha256']:bad.append(dict(module=r['module'],actual=h,expected=r['object_sha256']))
p=pathlib.Path('/home/dombarker/project-offloads/codex-pv-l2d-20261028/embedding');deps=[]
for m in ['AspisR1ProducerRelease47.Types','AspisR1ProducerRelease47.Funs','PV_L2B_Rejection','PV_L2B_SourceWords','PV_L2B_SamplerLaw']:
 s=p/'sources'/(m.replace('.','/')+'.lean');o=p/'objects'/(m.replace('.','/')+'.olean');assert s.is_file() and o.is_file()
 deps.append(dict(module=m,source_sha256=hashlib.sha256(s.read_bytes()).hexdigest(),object_sha256=hashlib.sha256(o.read_bytes()).hexdigest(),path=str(o)))
print(json.dumps(dict(external_count=len(x),mismatches=bad,dependencies=deps,environment=json.load(open(p/'J.json')),environment_sha256=hashlib.sha256((p/'J.json').read_bytes()).hexdigest())))
assert not bad
'''
q=subprocess.run(['ssh',host,'python3 -c '+shlex.quote(code)],input=json.dumps(x),text=True,capture_output=True)
(E/'final-preflight-transport.json').write_text(json.dumps(dict(exit=q.returncode,stderr=q.stderr),indent=2)+'\n');assert q.returncode==0,q.stderr
v=json.loads(q.stdout)
for d in v['dependencies']:
 receipts=[json.loads(p.read_text()) for p in E.glob('receipt-*.json')]
 receipt=next(r for r in receipts if r.get('target')==d['module'] and r['exit']==0)
 assert receipt['source_sha256']==d['source_sha256'];d['focused_receipt']=receipt['attempt']
v['source_revision']=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();v['importing_foreign_project_objects']=False
(E/'final-preflight.json').write_text(json.dumps(v,indent=2)+'\n');print('all',v['external_count'],'external objects match; five private project dependencies verified')

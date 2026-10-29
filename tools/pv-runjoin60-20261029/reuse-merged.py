from pathlib import Path
import json,subprocess,hashlib,shlex
R=Path(__file__).resolve().parents[2]; E=R/'evidence/pv-runjoin60-20261029'; plan=json.loads((E/'build-plan.json').read_text()); records={}
for job in ['pv-rjq-20261029','pv-rjn-20261029']:
 for p in (R/'evidence'/job).glob('modules-*.json'):
  for v in json.loads(p.read_text()):
   if v['accepted']: records[v['module']]=v
payload=[]
for m,v in records.items():
 path='docs/research/v8-r0-zk-20261009/lean/'+m.replace('.','/')+'.lean'; b=(R/path).read_bytes(); assert hashlib.sha256(b).hexdigest()==v['source_sha256']
 pin=dict(authority='h5 own git-tracked HEAD; h6 merged object reuse',path=path,git_blob=subprocess.check_output(['git','rev-parse','HEAD:'+path],text=True).strip(),sha256=v['source_sha256'],imports=list(v['dependencies']),revision=v['source_revision'])
 plan['modules'][m]=pin
 old=v['output_path'].split('/evidence/')[0]; obj=old+'/objects/'+m.replace('.','/')+'.olean'
 payload.append(dict(module=m,source=b.decode(),object=obj,sha256=v['object_sha256']))
code=r"""import json,sys,pathlib,hashlib
x=json.load(sys.stdin);p=pathlib.Path(x['workspace']);out=[]
for v in x['modules']:
 m=v['module'].replace('.','/');o=pathlib.Path(v['object']);assert hashlib.sha256(o.read_bytes()).hexdigest()==v['sha256'];s=p/'sources'/(m+'.lean');s.parent.mkdir(parents=True,exist_ok=True)
 if s.exists():assert s.read_text()==v['source']
 else:s.write_text(v['source'])
 for suffix in ['.olean','.olean.server','.olean.private','.ilean','.ir']:
  src=o.with_name(o.name[:-6]+suffix);dst=p/'objects'/(m+suffix)
  if src.exists():
   dst.parent.mkdir(parents=True,exist_ok=True)
   if dst.exists():assert hashlib.sha256(dst.read_bytes()).digest()==hashlib.sha256(src.read_bytes()).digest()
   else:dst.symlink_to(src)
 out.append(v['module'])
print(json.dumps(out))
"""
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(dict(workspace=plan['workspace'],modules=payload)),text=True,capture_output=True);(E/'merged-reuse.json').write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr,modules=payload),indent=2)+'\n');assert r.returncode==0,r.stderr
(E/'build-plan.json').write_text(json.dumps(plan,indent=2)+'\n')
print(r.stdout)

from pathlib import Path
import json,subprocess,shlex,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin62-20261029';plan=json.loads((E/'build-plan.json').read_text());want=json.loads((E/'native-dependency-plan.json').read_text())['order'];cache=json.loads((R/'evidence/pv-batch3-20261027/d336-cache-verification.json').read_text());rows={v['module']:v for v in cache['rows']};payload=[]
for v in want:
 m=v['module']
 if m in rows:
  row=rows[m];assert row['source_authority']['sha256']==v['pin']['sha256'],m
  payload.append(dict(module=m,pin=v['pin'],source=(R/v['pin']['path']).read_text(),cache=row))
code=r'''import json,sys,pathlib,hashlib
x=json.load(sys.stdin);p=pathlib.Path(x['workspace']);sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();out=[];accepted={}
env=json.load(open(p/'J.json'));old=json.load(open('/home/dombarker/project-offloads/codex-pv-batch3-20261027/env-J-private.json'));toolchain={k:env[k]==old.get(k) for k in env if k!='LEAN_PATH'}
for v in x['modules']:
 m=v['module'];row=v['cache'];o=pathlib.Path(row['object_path']);errors=[];deps={}
 if not o.exists():errors.append('missing object')
 elif sha(o)!=row['object_sha256']:errors.append('object hash mismatch')
 r=json.load(open(row['accepted_binding']['receipt']));assert r['exit_status']==0
 if r['source_sha256']!=v['pin']['sha256']:errors.append('receipt source mismatch')
 for d,dv in r['dependency_objects'].items():
  q=next((rt/(d.replace('.','/')+'.olean') for rt in [p/'objects',p/'external'] if (rt/(d.replace('.','/')+'.olean')).exists()),None)
  if q is None and d in accepted:q=pathlib.Path(accepted[d]['object_path'])
  h=sha(q) if q else None;deps[d]=dict(path=str(q),sha256=h)
  if h!=dv['sha256']:errors.append('dependency mismatch '+d)
 if not all(toolchain.values()):errors.append('toolchain mismatch')
 rec=dict(module=m,errors=errors,cache_object=str(o),dependencies=deps,toolchain=toolchain)
 if not errors:
  rel=m.replace('.','/');s=p/'sources'/(rel+'.lean');s.parent.mkdir(parents=True,exist_ok=True)
  if s.exists():assert s.read_text()==v['source']
  else:s.write_text(v['source'])
  for suffix in ['.olean','.olean.server','.olean.private','.ilean','.ir']:
   src=o.with_name(o.name[:-6]+suffix);dst=p/'objects'/(rel+suffix)
   if src.exists():
    dst.parent.mkdir(parents=True,exist_ok=True)
    if dst.exists():assert sha(dst)==sha(src)
    else:dst.symlink_to(src)
  accepted[m]=dict(module=m,source_sha256=v['pin']['sha256'],source_revision=v['pin']['revision'],object_path=str(p/'objects'/(rel+'.olean')),object_sha256=row['object_sha256'],dependencies=deps,accepted=True,axioms=r['print_axioms'],output_path=row['accepted_binding']['receipt'])
 out.append(rec)
print(json.dumps(dict(checks=out,records=accepted)))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(dict(workspace=plan['workspace'],modules=payload)),text=True,capture_output=True);assert r.returncode==0,r.stderr
result=json.loads(r.stdout);(E/'native-h6-reuse.json').write_text(json.dumps(result,indent=2)+'\n');reuse=json.loads((E/'open-inputs-reuse.json').read_text());reuse['records'].update(result['records']);(E/'open-inputs-reuse.json').write_text(json.dumps(reuse,indent=2)+'\n')
for v in payload:
 if v['module'] in result['records']:plan['modules'][v['module']]=v['pin']
(E/'build-plan.json').write_text(json.dumps(plan,indent=2)+'\n');print('Verified reuse',len(result['records']),'of',len(payload));print([(v['module'],v['errors']) for v in result['checks'] if v['errors']][:15])

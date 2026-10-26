from pathlib import Path
import json,hashlib,shutil
B=Path('/home/dombarker/project-offloads');T=B/'aspis-fs-generic-20261006/evidence';U=B/'codex-cx-import-union-20261022';source=B/'d18-s3-s9-cohort-recompile-v1-20261022/attempt23/attempt/objects';stage=U/'EJR-library-stage'
assert not stage.exists();rows=json.loads((T/'EJR_aeneas-complete-library-pins.json').read_text());verified=[];bad=[]
for r in rows:
 p=source/(r['module'].replace('.','/')+'.olean')
 if not p.is_file():bad.append(dict(module=r['module'],error='missing'));continue
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 if h!=r['sha256']:bad.append(dict(module=r['module'],error='hash mismatch',actual=h));continue
 comps=[]
 for c in r.get('companions',[]):
  suffix=c['path'].split('.olean',1)[1];cp=Path(str(p)+suffix)
  if not cp.is_file() or hashlib.sha256(cp.read_bytes()).hexdigest()!=c['sha256']:bad.append(dict(module=r['module'],error='companion missing/mismatch',path=str(cp)))
  else:comps.append(dict(source=str(cp),sha256=c['sha256'],suffix=suffix,bytes=c['bytes']))
 verified.append(dict(module=r['module'],sha256=h,bytes=p.stat().st_size,source=str(p),companions=comps))
assert {r['module'] for r in bad}=={'Aeneas.Std.Core.Fmt','Aeneas.Std.Array.ArraySlice'},bad
stage.mkdir()
for r in verified:
 dest=stage/(r['module'].replace('.','/')+'.olean');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(r['source'],dest)
 for c in r['companions']:shutil.copyfile(c['source'],str(dest)+c['suffix'])
report=dict(verified=verified,bad=bad,staged=str(stage),published=False,scope='same historical library object hashes; staged outside LEAN_PATH pending two source rebuilds')
(T/'EJR-library-staged.json').write_text(json.dumps(report,indent=2)+'\n');print('staged',len(verified),'missing',len(bad))

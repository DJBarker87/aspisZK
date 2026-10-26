from pathlib import Path
import json,hashlib,shutil,os
B=Path('/home/dombarker/project-offloads');T=B/'aspis-fs-generic-20261006/evidence';U=B/'codex-cx-import-union-20261022'
source=B/'d18-s3-s9-cohort-recompile-v1-20261022/attempt23/attempt/objects'
rows=json.loads((T/'EJR_aeneas-library-pins.json').read_text());verified=[];bad=[]
for r in rows:
 p=source/(r['module'].replace('.','/')+'.olean')
 if not p.is_file():bad.append(dict(module=r['module'],error='missing'));continue
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 if h!=r['sha256']:bad.append(dict(module=r['module'],error='hash mismatch',actual=h));continue
 verified.append(dict(module=r['module'],sha256=h,bytes=p.stat().st_size,source=str(p),historical_receipt='import-union-20261022/build-host/raw-object-pins.json'))
report=dict(verified=verified,bad=bad,operation='read-only surviving cache, restore identical pinned Aeneas library objects; no project object reused')
(T/'EJR-library-check.json').write_text(json.dumps(report,indent=2)+'\n')
print('verified',len(verified),'bad',len(bad),flush=True)
if bad:raise SystemExit(1)
stage=U/'EJR-library-stage';stage.mkdir(exist_ok=False)
for r in verified:
 rel=r['module'].replace('.','/')+'.olean';p=stage/rel;p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(r['source'],p)
 # Restore required split companions only when historical pin recorded one.
 pin=next(v for v in rows if v['module']==r['module'])
 for c in pin.get('companions',[]):
  raise RuntimeError('companion pin requires explicit handling: '+str(c))
target=U/'retained-objects';assert not (target/'Aeneas').exists();os.rename(stage/'Aeneas',target/'Aeneas');os.rename(stage/'Aeneas.olean',target/'Aeneas.olean');stage.rmdir()
report['restored_to']=str(target);(T/'EJR-library-check.json').write_text(json.dumps(report,indent=2)+'\n')

"""End-of-job removal of only this job's rebuildable caches, with receipt."""
from pathlib import Path
import subprocess,json,shlex,time
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-leaf-p6-15-20261027';H='dombarker@100.108.41.90'
script=f'''from pathlib import Path
import json,hashlib,shutil
b=Path({B!r});receipt=b/'LPq_CLEANUP.json'
assert not receipt.exists(),'cleanup already submitted; recover receipt'
paths=[b/'LPq_objects',b/'LPq_target',b/'LPq_tmp']
objects={{str(p.relative_to(b)):dict(bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in (b/'LPq_objects').rglob('*.olean')}}
tools={{}}
for p in [Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'),Path('/home/dombarker/.cargo/bin/cargo-kani')]:
 tools[str(p)]=dict(realpath=str(p.resolve()),sha256=hashlib.sha256(p.read_bytes()).hexdigest())
out=dict(paths=[str(p) for p in paths],private_object_manifest=objects,tools=tools,retained=['LPq_src symlink and underlying reused corpus','all shared/coherent/XRy caches','all sources/receipts/configs/library pins'],removed=[],status='started')
receipt.write_text(json.dumps(out,indent=2)+'\\n')
for p in paths:
 assert p.parent==b and not p.is_symlink()
 if p.exists():shutil.rmtree(p)
 out['removed'].append(str(p));receipt.write_text(json.dumps(out,indent=2)+'\\n')
out['status']='complete';out['verified_absent']=all(not p.exists() for p in paths)
receipt.write_text(json.dumps(out,indent=2)+'\\n')
print(json.dumps(dict(status=out['status'],verified_absent=out['verified_absent'],objects=len(objects))))
'''
argv=['ssh','-o','ConnectTimeout=15',H,'python3 -c '+shlex.quote(script)]
r=subprocess.run(argv,capture_output=True,text=True);(E/'LPq_CLEANUP_SUBMIT.json').write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr,script=script),indent=2)+'\n')
# Never reissue the submitted cleanup; receipt recovery is read-only.
for trial in range(11):
 r=subprocess.run(['ssh','-o','ConnectTimeout=15',H,'cat '+shlex.quote(B+'/LPq_CLEANUP.json')],capture_output=True,text=True)
 with (E/'LPq_CLEANUP_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(trial=trial,exit=r.returncode,stderr=r.stderr))+'\n')
 if r.returncode!=255:break
 if trial<10:time.sleep(60)
assert r.returncode==0,r.stderr
(E/'LPq_CLEANUP.json').write_text(r.stdout);out=json.loads(r.stdout)
assert out['status']=='complete' and out['verified_absent'];print(json.dumps(dict(status=out['status'],objects=len(out['private_object_manifest']))))

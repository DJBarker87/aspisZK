"""Read-only object pins for the accepted NNY overlay; no cache copying."""
from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent
v=json.loads((E/'NNY_VALIDATION.json').read_text())
modules=v['accepted_current_modules'];B='/home/dombarker/project-offloads/codex-cx-a2-20261108'
code='''from pathlib import Path
import json,hashlib
b=Path(%r);names=%r;out={}
for name in names:
 p=b/'NNY_objects'/(name.replace('.','/')+'.olean')
 assert p.is_file(),str(p)
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():out[str(z)]={'sha256':hashlib.sha256(z.read_bytes()).hexdigest(),'bytes':z.stat().st_size}
print(json.dumps(out))
'''%(B,list(modules))
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
 with (E/'NNY_PIN_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps({'retry':retry,'exit':r.returncode,'stderr':r.stderr,'read_only':True})+'\n')
 if r.returncode!=255:break
 if retry<10:time.sleep(60)
assert r.returncode==0,r.stderr
pins=json.loads(r.stdout)
(E/'NNY_OVERLAY.json').write_text(json.dumps({'path':B+'/NNY_objects','accepted_current_modules':modules,'objects':pins,'reference_only_paths':json.loads((E/'NNY_RUN5B_PATHS.json').read_text()),'seed_policy':'reference only; no copying/moving/deleting'},indent=2)+'\n')
print(json.dumps({'modules':len(modules),'object_files':len(pins),'overlay':B+'/NNY_objects'}))

"""Read-only object pins for the accepted NNU overlay; never copies binaries."""
from pathlib import Path
import hashlib,json,subprocess,time
E=Path(__file__).resolve().parent
v=json.loads((E/'NNU_VALIDATION.json').read_text())
B='/home/dombarker/project-offloads/codex-cx-a2-20261108/NNU_objects'
code="""from pathlib import Path
import hashlib,json
b=Path(%r);names=%r;out={}
for name in names:
 p=b/(name.replace('.','/')+'.olean');assert p.is_file(),name
 out[name]={}
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():out[name][str(q)]={'sha256':hashlib.sha256(q.read_bytes()).hexdigest(),'bytes':q.stat().st_size}
print(json.dumps(out))
""" % (B,sorted(v['accepted_current_modules']))
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
 with (E/'NNU_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps({'attempt':'NNU_FINAL_PINS','retry':retry,'exit':r.returncode,'submitted':False,'stderr':r.stderr})+'\n')
 if r.returncode!=255:break
 if retry<10:time.sleep(60)
assert r.returncode==0,r.stderr
pins=json.loads(r.stdout)
old=json.loads((E/'NNU_OVERLAY.json').read_text())
for name,objects in old['accepted_only'].items():
 for path,metadata in objects.items():assert pins[name][path]==metadata,(name,path)
(E/'NNU_OVERLAY.json').write_text(json.dumps({'overlay':B,'accepted_only':pins},indent=2)+'\n')
print(json.dumps({'accepted_modules':len(pins),'objects':sum(len(x) for x in pins.values())}))
